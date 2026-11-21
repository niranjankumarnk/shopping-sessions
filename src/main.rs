// Shopping Sessions: Rust implementation of rules.md.
//
// Shape: links are resolved on a side thread while events are parsed into buckets by event-id hash;
// each bucket is deduplicated with a small in-cache table; survivors are resolved to people and
// scattered into person partitions; each partition is sorted, sessionized, credited and written
// straight into Parquet pages (hand-written, uncompressed, PLAIN).
//
// Identity: event IDs use 104 bits of xxh3-128, user IDs 64 bits of xxh3; click IDs, person names
// and categories are compared as bytes.
use std::cell::UnsafeCell;
use std::fs::File;
use std::hash::{BuildHasherDefault, Hasher};
use std::io::{IoSlice, Write};
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::time::Instant;

use hashbrown::HashMap;
use memmap2::Mmap;
use rayon::prelude::*;
use xxhash_rust::xxh3::{xxh3_128, xxh3_64};

const DAY_MS: i64 = 86_400_000;
const GAP_MS: i64 = 1_800_000;
const WEEK_MS: i64 = 604_800_000;
const NO_CAT: u32 = u32::MAX;

#[derive(Default)]
struct IdHasher(u64);
impl Hasher for IdHasher {
    fn finish(&self) -> u64 { self.0 }
    fn write(&mut self, _: &[u8]) { unreachable!() }
    fn write_u64(&mut self, v: u64) { self.0 = v; }
}
type IdMap<V> = HashMap<u64, V, BuildHasherDefault<IdHasher>>;

struct Raw<T>(*mut T);
impl<T> Clone for Raw<T> { fn clone(&self) -> Self { *self } }
impl<T> Copy for Raw<T> {}
unsafe impl<T> Send for Raw<T> {}
unsafe impl<T> Sync for Raw<T> {}
impl<T> Raw<T> {
    #[inline(always)]
    fn get(self) -> *mut T { self.0 }
}

#[inline(always)]
fn prefetch<T>(p: *const T) {
    #[cfg(target_arch = "x86_64")]
    unsafe { core::arch::x86_64::_mm_prefetch(p as *const i8, core::arch::x86_64::_MM_HINT_T0) }
    #[cfg(target_arch = "aarch64")]
    unsafe { core::arch::asm!("prfm pldl1keep, [{0}]", in(reg) p, options(nostack, preserves_flags, readonly)) }
    #[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
    let _ = p;
}

// ---------------------------------------------------------------- packed byte-string references
// A reference into a mapped input file: pointer in the low 48 bits, length in the high 16.
// Strings of 65,535 bytes or more keep their length in a side table.
static LONG: Mutex<Vec<(usize, usize)>> = Mutex::new(Vec::new());
#[inline]
fn pack(b: &[u8]) -> u64 {
    let p = b.as_ptr() as u64;
    debug_assert!(p >> 48 == 0);
    if b.len() < 0xFFFF {
        p | ((b.len() as u64) << 48)
    } else {
        LONG.lock().unwrap().push((b.as_ptr() as usize, b.len()));
        p | (0xFFFFu64 << 48)
    }
}
#[inline]
fn unpack(v: u64) -> &'static [u8] {
    let p = (v & 0xFFFF_FFFF_FFFF) as usize;
    let mut len = (v >> 48) as usize;
    if len == 0xFFFF {
        len = LONG.lock().unwrap().iter().find(|e| e.0 == p).map(|e| e.1).unwrap();
    }
    unsafe { std::slice::from_raw_parts(p as *const u8, len) }
}

#[repr(C)]
#[derive(Clone, Copy)]
struct Ev { eid: u64, user: u64, name: u64, tp: u64, ingest: i32, cat: u16, eid2: u16 }
// `tp` packs the time since window_start (40 bits of milliseconds) above the price (24 bits);
// all ones marks an event that is invalid or lost its dedup.
const DEAD_TP: u64 = u64::MAX;
const PRICE_BITS: u32 = 24;
#[repr(C)]
#[derive(Clone, Copy)]
struct Sv { pk: u64, ts: i64, name: u64, price: u32, cat: u32 }
#[repr(C)]
#[derive(Clone, Copy)]
struct Ck { pk: u64, ts: i64, id: u64, camp: u32, pad: u32 }

// ---------------------------------------------------------------- line splitting
/// Reads one line starting at `*pos`, moves `*pos` past its `\n`, and returns its N fields with
/// whole-field quotes stripped. None if the line is malformed.
#[inline(always)]
fn split_line<'a, const N: usize>(data: &'a [u8], pos: &mut usize) -> Option<[&'a [u8]; N]> {
    let start = *pos;
    let len = data.len();
    let mut cuts = [0usize; N];
    let mut n = 0usize;
    let mut quote = false;
    let mut i = start;
    while i < len {
        let c = unsafe { *data.get_unchecked(i) };
        if c == b',' {
            if n < N { cuts[n] = i; }
            n += 1;
        } else if c == b'\n' {
            break;
        } else if c == b'"' {
            quote = true;
        }
        i += 1;
    }
    *pos = i + 1;
    if n != N - 1 { return None; }
    cuts[N - 1] = i;
    let mut out: [&[u8]; N] = [&[]; N];
    let mut s = start;
    for k in 0..N {
        let f = unsafe { data.get_unchecked(s..cuts[k]) };
        out[k] = f;
        s = cuts[k] + 1;
    }
    if quote {
        for f in out.iter_mut() {
            if !f.is_empty() && f[0] == b'"' {
                if f.len() < 2 || f[f.len() - 1] != b'"' { return None; }
                let inner = &f[1..f.len() - 1];
                if memchr::memchr(b'"', inner).is_some() { return None; }
                *f = inner;
            } else if memchr::memchr(b'"', f).is_some() {
                return None;
            }
        }
    }
    Some(out)
}

/// Three bit masks for one block of bytes: the commas, the newlines and the quotes.
/// Bit `i << MASK_SHIFT` is byte i.
#[cfg(target_arch = "x86_64")]
const BLOCK: usize = 64;
#[cfg(target_arch = "x86_64")]
const MASK_SHIFT: u32 = 0;
#[cfg(target_arch = "x86_64")]
#[inline(always)]
unsafe fn delim_masks(p: *const u8) -> (u64, u64, u64) {
    use core::arch::x86_64::*; // SSE2 is part of every x86-64 CPU
    let (c, n, q) = (_mm_set1_epi8(b',' as i8), _mm_set1_epi8(b'\n' as i8), _mm_set1_epi8(b'"' as i8));
    let (mut cm, mut nm, mut qm) = (0u64, 0u64, 0u64);
    for k in 0..4 {
        let v = _mm_loadu_si128(p.add(k * 16) as *const __m128i);
        cm |= (_mm_movemask_epi8(_mm_cmpeq_epi8(v, c)) as u32 as u64) << (k * 16);
        nm |= (_mm_movemask_epi8(_mm_cmpeq_epi8(v, n)) as u32 as u64) << (k * 16);
        qm |= (_mm_movemask_epi8(_mm_cmpeq_epi8(v, q)) as u32 as u64) << (k * 16);
    }
    (cm, nm, qm)
}
#[cfg(target_arch = "aarch64")]
const BLOCK: usize = 16;
#[cfg(target_arch = "aarch64")]
const MASK_SHIFT: u32 = 2;
#[cfg(target_arch = "aarch64")]
#[inline(always)]
unsafe fn delim_masks(p: *const u8) -> (u64, u64, u64) {
    use core::arch::aarch64::*;
    let v = vld1q_u8(p);
    // 4 bits per byte; keep one of them
    let nib = |x: uint8x16_t| vget_lane_u64::<0>(vreinterpret_u64_u8(vshrn_n_u16::<4>(vreinterpretq_u16_u8(x)))) & 0x8888_8888_8888_8888;
    (nib(vceqq_u8(v, vdupq_n_u8(b','))), nib(vceqq_u8(v, vdupq_n_u8(b'\n'))), nib(vceqq_u8(v, vdupq_n_u8(b'"'))))
}

/// The same three masks from two 32-byte loads. Only called from code compiled for AVX2.
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
#[inline]
unsafe fn wide_masks(p: *const u8) -> (u64, u64, u64) {
    use core::arch::x86_64::*;
    let (c, n, q) = (_mm256_set1_epi8(b',' as i8), _mm256_set1_epi8(b'\n' as i8), _mm256_set1_epi8(b'"' as i8));
    let v0 = _mm256_loadu_si256(p as *const __m256i);
    let v1 = _mm256_loadu_si256(p.add(32) as *const __m256i);
    let two = |a: __m256i, b: __m256i| (_mm256_movemask_epi8(a) as u32 as u64) | ((_mm256_movemask_epi8(b) as u32 as u64) << 32);
    (two(_mm256_cmpeq_epi8(v0, c), _mm256_cmpeq_epi8(v1, c)), two(_mm256_cmpeq_epi8(v0, n), _mm256_cmpeq_epi8(v1, n)), two(_mm256_cmpeq_epi8(v0, q), _mm256_cmpeq_epi8(v1, q)))
}
#[cfg(target_arch = "aarch64")]
#[inline(always)]
unsafe fn wide_masks(p: *const u8) -> (u64, u64, u64) { delim_masks(p) }

/// Calls `f` with the N fields of every well-formed line of `data`, whole-field quotes stripped.
/// `WIDE` picks the AVX2 masks; it may only be true inside code compiled for AVX2 (see `fast_cpu`).
/// Same rules as `split_line`. Only commas and newlines are visited one by one; quotes are counted
/// per line, and a line is well formed when every quote is the first or last byte of a field that
/// both starts and ends with one: quotes in the line == 2 x such fields.
///
/// The last partial block is scanned from a zero-padded copy, with a newline added after the
/// data if its last line has none, so every line ends in the one loop and `f` has one call site.
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
#[inline(always)]
fn scan_lines<'a, const N: usize, const WIDE: bool>(data: &'a [u8], mut f: impl FnMut([&'a [u8]; N])) {
    let len = data.len();
    let ptr = data.as_ptr();
    let mut cuts = [0usize; 9];
    assert!(N <= 8);
    let (mut n, mut line, mut qtot, mut qstart) = (0usize, 0usize, 0usize, 0usize);
    let whole = len / BLOCK;
    let rem = len - whole * BLOCK;
    let open = len > 0 && data[len - 1] != b'\n';
    let blocks = whole + (rem > 0 || open) as usize;
    let mut tail = [0u8; BLOCK];
    for bi in 0..blocks {
        let pos = bi * BLOCK;
        let src = if bi < whole {
            unsafe { ptr.add(pos) }
        } else {
            unsafe { std::ptr::copy_nonoverlapping(ptr.add(pos), tail.as_mut_ptr(), rem); }
            if open { tail[rem] = b'\n'; }
            tail.as_ptr()
        };
        let (cm, nm, qm) = unsafe { if WIDE { wide_masks(src) } else { delim_masks(src) } };
        let mut m = cm | nm;
        while m != 0 {
            let t = m.trailing_zeros();
            let i = pos + (t >> MASK_SHIFT) as usize;
            if (nm >> t) & 1 == 0 {
                unsafe { *cuts.get_unchecked_mut(n) = i; }
                n = (n + 1).min(N);
            } else {
                // a line ends at i (for an added newline, i is the length of the data)
                let seen = qtot + (qm & ((1u64 << t) - 1)).count_ones() as usize;
                let quotes = seen - qstart;
                qstart = seen;
                if n == N - 1 {
                    cuts[N - 1] = i;
                    let mut out: [&[u8]; N] = [&[]; N];
                    let mut a = line;
                    let mut nq = 0usize;
                    for k in 0..N {
                        let b = cuts[k];
                        let (mut x, mut y) = (a, b);
                        if b - a >= 2 {
                            let isq = unsafe { (*ptr.add(a) == b'"') & (*ptr.add(b - 1) == b'"') } as usize;
                            nq += isq;
                            x += isq;
                            y -= isq;
                        }
                        out[k] = unsafe { std::slice::from_raw_parts(ptr.add(x), y - x) };
                        a = b + 1;
                    }
                    if quotes == 2 * nq { f(out); }
                }
                n = 0;
                line = i + 1;
            }
            m &= m - 1;
        }
        qtot += qm.count_ones() as usize;
    }
}
/// Other architectures: the plain scanner.
#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
#[inline(always)]
fn scan_lines<'a, const N: usize, const WIDE: bool>(data: &'a [u8], mut f: impl FnMut([&'a [u8]; N])) {
    let mut pos = 0;
    while pos < data.len() {
        if let Some(x) = split_line::<N>(data, &mut pos) { f(x); }
    }
}

fn chunks(data: &'static [u8], chunk: usize) -> Vec<&'static [u8]> {
    // Skip the header line, then cut at line starts.
    let body = match memchr::memchr(b'\n', data) { Some(p) => p + 1, None => data.len() };
    let mut cuts = vec![body];
    let mut p = body + chunk;
    while p < data.len() {
        match memchr::memchr(b'\n', &data[p..]) {
            Some(q) => { cuts.push(p + q + 1); p = p + q + 1 + chunk; }
            None => break,
        }
    }
    cuts.push(data.len());
    cuts.windows(2).filter(|w| w[0] < w[1]).map(|w| &data[w[0]..w[1]]).collect()
}

// ---------------------------------------------------------------- timestamps
#[inline]
fn days_from_civil(y: i64, m: i64, d: i64) -> i64 {
    let y = if m <= 2 { y - 1 } else { y };
    let era = if y >= 0 { y } else { y - 399 } / 400;
    let yoe = y - era * 400;
    let doy = (153 * (if m > 2 { m - 3 } else { m + 9 }) + 2) / 5 + d - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * 146097 + doe - 719468
}
// Eight bytes of a timestamp at a time. XOR with the expected layout ('0' where a digit goes, the
// separator elsewhere) leaves each digit's value, and 0 for a correct separator; `ok8` then checks
// every digit is 0-9 and every separator matched.
const fn le(b: [u8; 8]) -> u64 { u64::from_le_bytes(b) }
const DIG: u8 = 6;   // a digit byte passes when value + 6 stays under 16
const SEP: u8 = 15;  // a separator byte passes only when the XOR left 0
const HI: u64 = 0xF0F0_F0F0_F0F0_F0F0;
#[inline(always)]
fn ld8(s: &[u8], i: usize) -> u64 { debug_assert!(i + 8 <= s.len()); unsafe { (s.as_ptr().add(i) as *const u64).read_unaligned() }.to_le() }
#[inline(always)]
fn ok8(t: u64, add: u64) -> bool { (t | t.wrapping_add(add)) & HI == 0 }
/// Byte k of the result is digit k * 10 + digit k+1.
#[inline(always)]
fn pairs(t: u64) -> u64 { t.wrapping_mul(10).wrapping_add(t >> 8) }
#[inline(always)]
fn byte(v: u64, k: u32) -> i64 { ((v >> (8 * k)) & 0xFF) as i64 }
static DIM: [i64; 16] = [0, 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31, 0, 0, 0];

/// The dates already validated, keyed by their ten bytes (`YYYY-MM-DD`), one slot per day of the
/// month. A data set holds a few weeks of dates, so nearly every timestamp finds its date here
/// and skips the calendar arithmetic.
struct DateCache { key0: [u64; 32], key1: [u16; 32], secs: [i64; 32] }
impl DateCache {
    fn new() -> DateCache { DateCache { key0: [0; 32], key1: [0; 32], secs: [0; 32] } }
}

/// Epoch milliseconds, or None for a bad timestamp (window not checked here).
#[inline(always)]
fn parse_ts(s: &[u8], dc: &mut DateCache) -> Option<i64> {
    let n = s.len();
    if (n == 20 || n == 25) && s[4] == b'-' {
        // YYYY-MM- | DDTHH:MM | then H:MM:SSZ (F1) or SS+HH:MM after a ':' (F2)
        let k0 = ld8(s, 0);
        let k1 = u16::from_le_bytes([s[8], s[9]]);
        let slot = (((s[8] & 3) * 10 + (s[9] & 15)) & 31) as usize;
        let t1 = ld8(s, 8) ^ le([b'0', b'0', b'T', b'0', b'0', b':', b'0', b'0']);
        let mut ok = ok8(t1, le([DIG, DIG, SEP, DIG, DIG, SEP, DIG, DIG]));
        let p1 = pairs(t1);
        let (h, mi) = (byte(p1, 3), byte(p1, 6));
        let hit = (dc.key0[slot] == k0) & (dc.key1[slot] == k1);
        let day_secs = if hit {
            dc.secs[slot]
        } else {
            let t0 = k0 ^ le([b'0', b'0', b'0', b'0', b'-', b'0', b'0', b'-']);
            let p0 = pairs(t0);
            let (cc, yy, mo) = (byte(p0, 0), byte(p0, 2), byte(p0, 5));
            let d = byte(p1, 0);
            let leap = if yy != 0 { yy & 3 == 0 } else { cc & 3 == 0 };
            let dim = DIM[(mo & 15) as usize] + ((mo == 2) & leap) as i64;
            ok &= ok8(t0, le([DIG, DIG, DIG, DIG, SEP, DIG, DIG, SEP])) & (mo >= 1) & (mo <= 12) & (d >= 1) & (d <= dim);
            if !ok { return None; }
            days_from_civil(cc * 100 + yy, mo, d) * 86400
        };
        let (se, off);
        if n == 20 {
            let t2 = ld8(s, 12) ^ le([b'0', b':', b'0', b'0', b':', b'0', b'0', b'Z']);
            ok &= ok8(t2, le([DIG, SEP, DIG, DIG, SEP, DIG, DIG, SEP]));
            se = byte(pairs(t2), 5);
            off = 0;
        } else {
            let sign = s[19];
            let t2 = ld8(s, 17) ^ (le([b'0', b'0', 0, b'0', b'0', b':', b'0', b'0']) | ((sign as u64) << 16));
            ok &= ok8(t2, le([DIG, DIG, SEP, DIG, DIG, SEP, DIG, DIG])) & (s[16] == b':') & ((sign == b'+') | (sign == b'-'));
            let p2 = pairs(t2);
            se = byte(p2, 0);
            let (oh, om) = (byte(p2, 3), byte(p2, 6));
            ok &= (oh <= 23) & (om <= 59);
            off = if sign == b'+' { oh * 3600 + om * 60 } else { -(oh * 3600 + om * 60) };
        }
        ok &= (h <= 23) & (mi <= 59) & (se <= 59);
        if !ok { return None; }
        if !hit {
            // the whole timestamp is valid, so its date is
            dc.key0[slot] = k0;
            dc.key1[slot] = k1;
            dc.secs[slot] = day_secs;
        }
        return Some((day_secs + h * 3600 + mi * 60 + se - off) * 1000);
    }
    // F3: ASCII digits only.
    if n == 0 { return None; }
    let mut i = 0;
    while i < n && s[i] == b'0' { i += 1; }
    let mut v: i64 = 0;
    let digits = n - i;
    if digits > 18 {
        // too long for any window: bad either way, digits or not
        return None;
    }
    for &c in &s[i..] {
        let d = c.wrapping_sub(b'0');
        if d > 9 { return None; }
        v = v * 10 + d as i64;
    }
    Some(v)
}
/// The straightforward parser the fast one is checked against.
#[cfg(test)]
fn parse_ts_ref(s: &[u8]) -> Option<i64> {
    fn d2(b: &[u8], i: usize) -> Option<i64> {
        let (a, c) = (b[i].wrapping_sub(b'0'), b[i + 1].wrapping_sub(b'0'));
        if a > 9 || c > 9 { None } else { Some((a * 10 + c) as i64) }
    }
    let n = s.len();
    if n == 0 { return None; }
    if (n == 20 || n == 25) && s[4] == b'-' {
        if s[7] != b'-' || s[10] != b'T' || s[13] != b':' || s[16] != b':' { return None; }
        let y = d2(s, 0)? * 100 + d2(s, 2)?;
        let (mo, d, h, mi, se) = (d2(s, 5)?, d2(s, 8)?, d2(s, 11)?, d2(s, 14)?, d2(s, 17)?);
        if mo < 1 || mo > 12 || d < 1 || h > 23 || mi > 59 || se > 59 { return None; }
        let leap = (y % 4 == 0 && y % 100 != 0) || y % 400 == 0;
        let dim = match mo { 2 => if leap { 29 } else { 28 }, 4 | 6 | 9 | 11 => 30, _ => 31 };
        if d > dim { return None; }
        let secs = days_from_civil(y, mo, d) * 86400 + h * 3600 + mi * 60 + se;
        if n == 20 {
            return if s[19] == b'Z' { Some(secs * 1000) } else { None };
        }
        let sign = match s[19] { b'+' => 1, b'-' => -1, _ => return None };
        if s[22] != b':' { return None; }
        let (oh, om) = (d2(s, 20)?, d2(s, 23)?);
        if oh > 23 || om > 59 { return None; }
        return Some((secs - sign * (oh * 3600 + om * 60)) * 1000);
    }
    let mut i = 0;
    while i < n && s[i] == b'0' { i += 1; }
    let mut v: i64 = 0;
    let digits = n - i;
    for &c in &s[i..] {
        let d = c.wrapping_sub(b'0');
        if d > 9 { return None; }
        if digits <= 18 { v = v * 10 + d as i64; }
    }
    if digits > 18 { None } else { Some(v) }
}
#[cfg(test)]
mod tests {
    use super::*;
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 { self.0 ^= self.0 << 13; self.0 ^= self.0 >> 7; self.0 ^= self.0 << 17; self.0 }
        fn below(&mut self, n: u64) -> u64 { self.next() % n }
    }
    #[test]
    fn fast_timestamps_match_reference() {
        let mut r = Rng(0x9E3779B97F4A7C15);
        let junk = b"0123456789-:TZtz+ .,\"\xff\x00/;aA";
        let mut checked = 0u64;
        let mut valid = 0u64;
        let mut dc = DateCache::new();
        let mut hits = 0u64;
        for round in 0..6_000_000u64 {
            let mut s: Vec<u8> = match r.below(4) {
                0 => format!("{:04}-{:02}-{:02}T{:02}:{:02}:{:02}Z", 1990 + r.below(60), r.below(14), r.below(33), r.below(26), r.below(62), r.below(62)).into_bytes(),
                1 => format!("{:04}-{:02}-{:02}T{:02}:{:02}:{:02}{}{:02}:{:02}", r.below(10000), 1 + r.below(12), 1 + r.below(31), r.below(24), r.below(60), r.below(60),
                             if r.below(2) == 0 { '+' } else { '-' }, r.below(25), r.below(61)).into_bytes(),
                2 => { let n = 1 + r.below(21); (0..n).map(|k| if k < 3 && r.below(3) == 0 { b'0' } else { b'0' + r.below(10) as u8 }).collect() }
                _ => format!("{:04}-{:02}-{:02}T{:02}:{:02}:{:02}Z", 2024 + r.below(5), 1 + r.below(12), 1 + r.below(29), r.below(24), r.below(60), r.below(60)).into_bytes(),
            };
            // mutate some of them
            if round % 3 == 0 && !s.is_empty() {
                for _ in 0..1 + r.below(2) {
                    let i = r.below(s.len() as u64) as usize;
                    match r.below(4) {
                        0 => s[i] = junk[r.below(junk.len() as u64) as usize],
                        1 => { s.remove(i); }
                        2 => s.insert(i, junk[r.below(junk.len() as u64) as usize]),
                        _ => s[i] = s[i].wrapping_add(1),
                    }
                    if s.is_empty() { break; }
                }
            }
            let (a, b) = (parse_ts(&s, &mut dc), parse_ts_ref(&s));
            assert_eq!(a, b, "{:?}", String::from_utf8_lossy(&s));
            assert_eq!(parse_ts(&s, &mut DateCache::new()), b, "fresh cache {:?}", String::from_utf8_lossy(&s));
            hits += (a.is_some() && s.len() >= 20 && s[4] == b'-') as u64;
            checked += 1;
            valid += a.is_some() as u64;
        }
        assert!(valid > checked / 4 && valid < checked && hits > checked / 8);
        for s in [&b""[..], b"2028-02-29T00:00:00Z", b"2027-02-29T00:00:00Z", b"2100-02-29T00:00:00Z", b"2000-02-29T23:59:59+00:00", b"2026-10-03T19:58:10-04:00",
                  b"2026-10-03T23:58:10Z", b"1791071890000", b"0001791071890000", b"2026-10-03T23:58:10z", b"2026-10-03t23:58:10Z", b"2026-10-03T24:00:00Z",
                  b"2026-10-03T23:58:60Z", b"2026-13-03T23:58:10Z", b"2026-10-03T23:58:10+24:00", b"2026-10-03T23:58:10+05:60", b"2026-10-03T23:58:10-00:00",
                  b"2026-10-03T23:58:10+0200x", b"00000000000000000000", b"99999999999999999999", b"0000-0000000000000000", b"1.79e12", b"-5", b"86400000"] {
            assert_eq!(parse_ts(s, &mut dc), parse_ts_ref(s), "{:?}", String::from_utf8_lossy(s));
            assert_eq!(parse_ts(s, &mut dc), parse_ts_ref(s), "second time {:?}", String::from_utf8_lossy(s));
        }
    }
    #[test]
    fn scanner_matches_split_line() {
        let mut r = Rng(42);
        #[allow(unused_mut, unused_variables)]
        let mut wide_runs = 0u64;
        let alphabet = b"ab,,,\"\"\n\n1 \r";
        for _ in 0..200_000 {
            let n = r.below(200) as usize;
            let data: Vec<u8> = (0..n).map(|_| alphabet[r.below(alphabet.len() as u64) as usize]).collect();
            for fields in [2usize, 4, 7] {
                let mut got: Vec<Vec<Vec<u8>>> = Vec::new();
                let mut want: Vec<Vec<Vec<u8>>> = Vec::new();
                macro_rules! run { ($n:literal) => {{
                    scan_lines::<$n, false>(&data, |f| got.push(f.iter().map(|x| x.to_vec()).collect()));
                    if fast_cpu() {
                        let mut wide: Vec<Vec<Vec<u8>>> = Vec::new();
                        #[cfg(target_arch = "x86_64")]
                        {
                            #[target_feature(enable = "avx2,bmi1,bmi2,popcnt")]
                            unsafe fn go(data: &[u8], wide: &mut Vec<Vec<Vec<u8>>>) { scan_lines::<$n, true>(data, |f| wide.push(f.iter().map(|x| x.to_vec()).collect())); }
                            unsafe { go(&data, &mut wide) };
                            wide_runs += 1;
                        }
                        #[cfg(not(target_arch = "x86_64"))]
                        scan_lines::<$n, true>(&data, |f| wide.push(f.iter().map(|x| x.to_vec()).collect()));
                        assert_eq!(wide, got, "wide {:?}", String::from_utf8_lossy(&data));
                    }
                    let mut pos = 0;
                    while pos < data.len() { if let Some(f) = split_line::<$n>(&data, &mut pos) { want.push(f.iter().map(|x| x.to_vec()).collect()); } }
                }}; }
                match fields { 2 => run!(2), 4 => run!(4), _ => run!(7) }
                assert_eq!(got, want, "{:?}", String::from_utf8_lossy(&data));
            }
        }
    }
}
#[inline]
fn parse_price(s: &[u8]) -> Option<u32> {
    if s.is_empty() { return None; }
    let mut i = 0;
    while i < s.len() && s[i] == b'0' { i += 1; }
    let rest = &s[i..];
    if rest.is_empty() || rest.len() > 8 { return None; } // all zeros, or over 99,999,999, or not digits
    let mut v: u32 = 0;
    for &c in rest {
        let d = c.wrapping_sub(b'0');
        if d > 9 { return None; }
        v = v * 10 + d as u32;
    }
    if v >= 1 && v <= 10_000_000 { Some(v) } else { None }
}

// ---------------------------------------------------------------- inputs
fn list_csv(dir: &Path) -> Vec<PathBuf> {
    let mut v: Vec<PathBuf> = match std::fs::read_dir(dir) {
        Ok(rd) => rd.filter_map(|e| e.ok()).map(|e| e.path())
            .filter(|p| p.extension().map_or(false, |x| x == "csv") && p.is_file()).collect(),
        Err(_) => vec![],
    };
    v.sort();
    v
}
/// Large regions that stay in use until the output is written and are never handed back to the
/// allocator: the mapped inputs and the biggest arrays. `release_regions` returns them to the
/// kernel on all threads just before exit, so the single-threaded teardown has little left to do.
static REGIONS: Mutex<Vec<(usize, usize)>> = Mutex::new(Vec::new());
fn note_region(start: usize, len: usize) { REGIONS.lock().unwrap().push((start, len)); }
fn note_vec<T>(v: &Vec<T>) { note_region(v.as_ptr() as usize, v.capacity() * std::mem::size_of::<T>()); }
fn release_regions() {
    #[cfg(target_os = "linux")]
    {
        const PAGE: usize = 4096;
        const HUGE: usize = 2 << 20;
        let regions = std::mem::take(&mut *REGIONS.lock().unwrap());
        let mut pieces: Vec<(usize, usize)> = Vec::new();
        for (start, len) in regions {
            let (a, b) = ((start + PAGE - 1) & !(PAGE - 1), (start + len) & !(PAGE - 1));
            let mut p = a;
            while p < b {
                // cut on 2 MB boundaries so no huge page is split between two pieces
                let q = (((p + (32 << 20)) & !(HUGE - 1)).max(p + PAGE)).min(b);
                pieces.push((p, q - p));
                p = q;
            }
        }
        pieces.par_iter().for_each(|&(p, l)| unsafe { libc::madvise(p as *mut libc::c_void, l, libc::MADV_DONTNEED); });
    }
}

fn map_file(p: &Path) -> Option<&'static [u8]> {
    let f = File::open(p).ok()?;
    if f.metadata().ok()?.len() == 0 { return None; }
    let m = unsafe { Mmap::map(&f).ok()? };
    #[cfg(unix)]
    let _ = m.advise(memmap2::Advice::Sequential);
    let s: &'static [u8] = unsafe { std::slice::from_raw_parts(m.as_ptr(), m.len()) };
    note_region(m.as_ptr() as usize, (m.len() + 4095) & !4095);
    std::mem::forget(m); // mapped for the life of the process
    Some(s)
}
fn map_dir(dir: &Path) -> Vec<&'static [u8]> {
    list_csv(dir).par_iter().filter_map(|p| map_file(p)).collect()
}
fn manifest_ts(text: &str, key: &str) -> i64 {
    let p = text.find(key).expect("manifest key");
    let rest = &text[p + key.len()..];
    let a = rest.find(':').unwrap();
    let rest = &rest[a + 1..];
    let q1 = rest.find('"').unwrap();
    let q2 = rest[q1 + 1..].find('"').unwrap();
    parse_ts(rest[q1 + 1..q1 + 1 + q2].as_bytes(), &mut DateCache::new()).expect("manifest timestamp")
}

// ---------------------------------------------------------------- links
/// user-id hash -> (person key, person name); open addressing, a slot is empty when its name is 0.
struct LinkTab { mask: usize, slots: Vec<[u64; 4]> }
impl LinkTab {
    #[inline(always)]
    fn slot(&self, h: u64) -> *const [u64; 4] { unsafe { self.slots.as_ptr().add(h as usize & self.mask) } }
    /// The person for a user ID: its hash and its own packed name are the fallback.
    #[inline(always)]
    fn person(&self, h: u64, own: u64) -> (u64, u64) {
        let mut i = h as usize & self.mask;
        loop {
            let s = unsafe { self.slots.get_unchecked(i) };
            if s[2] == 0 { return (h, own); }
            if s[0] == h { return (s[1], s[2]); }
            i = (i + 1) & self.mask;
        }
    }
}

/// One link line: each ID as its hash, its packed name, and its first 16 bytes as a number.
#[repr(C)]
#[derive(Clone, Copy)]
struct Pair { ka: u128, kb: u128, ha: u64, na: u64, hb: u64, nb: u64 }
/// Union-find node. On a root, `name` and `key` are the byte-wise smallest name of its set and
/// `size` is the set's size.
#[repr(C)]
#[derive(Clone, Copy)]
struct Node { key: u128, name: u64, parent: u32, size: u32 }

/// The first 16 bytes of a name, zero-padded, as a big-endian number: two names whose keys differ
/// compare byte-wise the way their keys do.
#[inline(always)]
fn prefix_key(b: &[u8]) -> u128 {
    let mut x = [0u8; 16];
    let n = b.len().min(16);
    x[..n].copy_from_slice(&b[..n]);
    u128::from_be_bytes(x)
}
#[inline(always)]
fn name_less(ka: u128, na: u64, kb: u128, nb: u64) -> bool {
    if ka != kb { ka < kb } else { unpack(na) < unpack(nb) }
}
/// The hash of a packed name, taken from its key when the whole name is in the key.
#[inline(always)]
fn name_hash(key: u128, name: u64) -> u64 {
    let len = (name >> 48) as usize;
    if len <= 16 { xxh3_64(&key.to_be_bytes()[..len]) } else { xxh3_64(unpack(name)) }
}

/// Builds the link table. Runs on a side thread while the events are parsed. The one-thread part
/// (numbering the IDs and joining them) works a small batch at a time so that its table and node
/// reads can be prefetched; resolving every ID to its person and filling the table runs on all
/// threads.
fn build_links(dir: PathBuf) -> LinkTab {
    let t0 = Instant::now();
    let files = map_dir(&dir);
    let parts: Vec<&'static [u8]> = files.iter().flat_map(|d| chunks(d, 4 << 20)).collect();
    let pairs: Vec<Vec<Pair>> = parts.par_iter().map(|part| {
        let mut v = Vec::with_capacity(part.len() / 16 + 4);
        scan_lines::<2, false>(part, |[a, b]| {
            if a.is_empty() || b.is_empty() { return; }
            v.push(Pair { ka: prefix_key(a), kb: prefix_key(b), ha: xxh3_64(a), na: pack(a), hb: xxh3_64(b), nb: pack(b) });
        });
        v
    }).collect();
    let npairs: usize = pairs.iter().map(|v| v.len()).sum();
    let t_pairs = t0.elapsed().as_secs_f64();

    // ---- number the distinct IDs and join each pair, one thread
    let cap = (npairs * 3).next_power_of_two().max(16);
    let mask = cap - 1;
    let mut tab: Vec<[u64; 2]> = vec![[0u64; 2]; cap]; // (hash, number + 1), open addressing
    advise_huge(&tab);
    let mut nodes: Vec<Node> = Vec::with_capacity(npairs * 2 + 1);
    let mut keys: Vec<u64> = Vec::with_capacity(npairs * 2 + 1);
    advise_huge(&nodes);
    #[inline(always)]
    fn intern(tab: &mut [[u64; 2]], mask: usize, nodes: &mut Vec<Node>, keys: &mut Vec<u64>, h: u64, name: u64, key: u128) -> u32 {
        let mut s = h as usize & mask;
        loop {
            let e = unsafe { *tab.get_unchecked(s) };
            if e[1] == 0 {
                let id = nodes.len() as u32;
                unsafe { *tab.get_unchecked_mut(s) = [h, id as u64 + 1]; }
                nodes.push(Node { key, name, parent: id, size: 1 });
                keys.push(h);
                return id;
            }
            if e[0] == h { return (e[1] - 1) as u32; }
            s = (s + 1) & mask;
        }
    }
    #[inline(always)]
    fn find(nodes: &mut [Node], mut x: u32) -> u32 {
        loop {
            let p = nodes[x as usize].parent;
            if p == x { return x; }
            let g = nodes[p as usize].parent;
            nodes[x as usize].parent = g; // path halving
            x = g;
        }
    }
    const BATCH: usize = 16;
    let mut ids = [(0u32, 0u32); BATCH];
    for v in &pairs {
        for blk in v.chunks(BATCH) {
            for p in blk {
                prefetch(tab.as_ptr().wrapping_add(p.ha as usize & mask));
                prefetch(tab.as_ptr().wrapping_add(p.hb as usize & mask));
            }
            for (k, p) in blk.iter().enumerate() {
                let ia = intern(&mut tab, mask, &mut nodes, &mut keys, p.ha, p.na, p.ka);
                let ib = intern(&mut tab, mask, &mut nodes, &mut keys, p.hb, p.nb, p.kb);
                ids[k] = (ia, ib);
                prefetch(nodes.as_ptr().wrapping_add(ia as usize));
                prefetch(nodes.as_ptr().wrapping_add(ib as usize));
            }
            for &(ia, ib) in &ids[..blk.len()] {
                let (mut ra, mut rb) = (find(&mut nodes, ia), find(&mut nodes, ib));
                if ra == rb { continue; }
                if nodes[ra as usize].size < nodes[rb as usize].size { std::mem::swap(&mut ra, &mut rb); }
                // the smaller set joins the larger; the root keeps the smaller of the two best names
                let b = nodes[rb as usize];
                nodes[rb as usize].parent = ra;
                let a = &mut nodes[ra as usize];
                a.size += b.size;
                if name_less(b.key, b.name, a.key, a.name) { a.key = b.key; a.name = b.name; }
            }
        }
    }
    let t_joined = t0.elapsed().as_secs_f64();

    // ---- every ID -> (person key, person name), on all threads
    let n = nodes.len();
    let tcap = (n * 2).next_power_of_two().max(16);
    let tmask = tcap - 1;
    let mut slots = vec![[0u64; 4]; tcap];
    advise_huge(&slots);
    note_vec(&slots);
    let slots_ptr = Raw(slots.as_mut_ptr());
    let (nodes_ref, keys_ref) = (&nodes, &keys);
    const STEP: usize = 8192;
    (0..n.div_ceil(STEP)).into_par_iter().for_each(|c| {
        let (lo, hi) = (c * STEP, ((c + 1) * STEP).min(n));
        let mut i = lo;
        while i < hi {
            let end = (i + BATCH).min(hi);
            for k in i..end {
                prefetch(nodes_ref.as_ptr().wrapping_add(nodes_ref[k].parent as usize));
                prefetch(slots_ptr.get().wrapping_add(keys_ref[k] as usize & tmask));
            }
            for k in i..end {
                let mut r = k;
                loop {
                    let p = nodes_ref[r].parent as usize;
                    if p == r { break; }
                    r = p;
                }
                let root = &nodes_ref[r];
                let (h, pk, name) = (keys_ref[k], name_hash(root.key, root.name), root.name);
                // claim the first free slot by its name word; nobody reads the other words until
                // every thread is done
                let mut s = h as usize & tmask;
                loop {
                    let slot = unsafe { slots_ptr.get().add(s) };
                    let name_word = unsafe { std::sync::atomic::AtomicU64::from_ptr(std::ptr::addr_of_mut!((*slot)[2])) };
                    if name_word.compare_exchange(0, name, std::sync::atomic::Ordering::AcqRel, std::sync::atomic::Ordering::Relaxed).is_ok() {
                        unsafe {
                            std::ptr::addr_of_mut!((*slot)[0]).write(h);
                            std::ptr::addr_of_mut!((*slot)[1]).write(pk);
                        }
                        break;
                    }
                    s = (s + 1) & tmask;
                }
            }
            i = end;
        }
    });
    eprintln!("          links: {} pairs parsed at {:.3}s, {} ids joined at {:.3}s, table filled at {:.3}s", npairs, t_pairs, n, t_joined, t0.elapsed().as_secs_f64());
    // the working memory is dead: give its pages back from this thread, not at exit
    release_pages(&tab);
    release_pages(&nodes);
    release_pages(&keys);
    for v in &pairs { release_pages(v); }
    LinkTab { mask: tmask, slots }
}

// ---------------------------------------------------------------- Parquet, by hand
struct Thrift { b: Vec<u8>, last: Vec<i16> }
impl Thrift {
    fn new() -> Thrift { Thrift { b: Vec::new(), last: vec![0] } }
    fn varint(&mut self, mut v: u64) {
        while v >= 0x80 { self.b.push((v as u8) | 0x80); v >>= 7; }
        self.b.push(v as u8);
    }
    fn zigzag(&mut self, v: i64) { self.varint(((v << 1) ^ (v >> 63)) as u64); }
    fn field(&mut self, id: i16, ty: u8) {
        let last = self.last.last_mut().unwrap();
        let delta = id - *last;
        *last = id;
        if delta > 0 && delta <= 15 { self.b.push(((delta as u8) << 4) | ty); } else { self.b.push(ty); self.zigzag(id as i64); }
    }
    fn i32(&mut self, id: i16, v: i32) { self.field(id, 5); self.zigzag(v as i64); }
    fn i64(&mut self, id: i16, v: i64) { self.field(id, 6); self.zigzag(v); }
    fn bytes(&mut self, v: &[u8]) { self.varint(v.len() as u64); self.b.extend_from_slice(v); }
    fn binary(&mut self, id: i16, v: &[u8]) { self.field(id, 8); self.bytes(v); }
    fn list(&mut self, id: i16, elem: u8, n: usize) {
        self.field(id, 9);
        if n < 15 { self.b.push(((n as u8) << 4) | elem); } else { self.b.push(0xF0 | elem); self.varint(n as u64); }
    }
    fn begin(&mut self) { self.last.push(0); }
    fn begin_field(&mut self, id: i16) { self.field(id, 12); self.last.push(0); }
    fn end(&mut self) { self.b.push(0); self.last.pop(); }
}

const T_INT32: i32 = 1;
const T_INT64: i32 = 2;
const T_BYTES: i32 = 6;
struct Col { name: &'static str, ty: i32, utf8: bool, date: bool, optional: bool }
/// One data page: `nvals` values whose body is the concatenation of `body`.
struct Page<'a> { nvals: usize, body: [&'a [u8]; 2] }

/// Writes all the slices with as few system calls as possible.
fn write_all_slices(f: &mut File, bufs: &[&[u8]]) {
    for batch in bufs.chunks(1000) {
        let io: Vec<IoSlice> = batch.iter().map(|b| IoSlice::new(b)).collect();
        let want: usize = batch.iter().map(|b| b.len()).sum();
        let mut done = f.write_vectored(&io).unwrap();
        if done < want {
            // a short write: finish the batch slice by slice
            for b in batch {
                if done >= b.len() { done -= b.len(); continue; }
                f.write_all(&b[done..]).unwrap();
                done = 0;
            }
        }
    }
}

/// Writes one Parquet file with at most one row group; `pages[c]` are column c's pages in row order.
/// The page bodies are written from where they are; only headers and the footer are built here.
fn write_parquet(path: &Path, cols: &[Col], nrows: usize, pages: &[Vec<Page>]) {
    let mut headers: Vec<Vec<u8>> = Vec::new();
    let mut chunks_meta: Vec<(usize, usize)> = Vec::new(); // (first page offset, bytes)
    let mut pos = 4usize;
    for col in pages {
        let start = pos;
        for p in col {
            let size = p.body[0].len() + p.body[1].len();
            let mut h = Thrift::new();
            h.i32(1, 0); // DATA_PAGE
            h.i32(2, size as i32);
            h.i32(3, size as i32);
            h.begin_field(5);
            h.i32(1, p.nvals as i32);
            h.i32(2, 0); // PLAIN
            h.i32(3, 3); // definition levels: RLE
            h.i32(4, 3); // repetition levels: RLE
            h.end();
            h.b.push(0);
            pos += h.b.len() + size;
            headers.push(h.b);
        }
        chunks_meta.push((start, pos - start));
    }
    let mut t = Thrift::new();
    t.i32(1, 1); // version
    t.list(2, 12, cols.len() + 1);
    t.begin();
    t.binary(4, b"schema");
    t.i32(5, cols.len() as i32);
    t.end();
    for c in cols {
        t.begin();
        t.i32(1, c.ty);
        t.i32(3, c.optional as i32);
        t.binary(4, c.name.as_bytes());
        if c.utf8 { t.i32(6, 0); }
        if c.date { t.i32(6, 6); }
        if c.utf8 { t.begin_field(10); t.begin_field(1); t.end(); t.end(); }
        if c.date { t.begin_field(10); t.begin_field(6); t.end(); t.end(); }
        t.end();
    }
    t.i64(3, nrows as i64);
    if nrows == 0 {
        t.list(4, 12, 0);
    } else {
        t.list(4, 12, 1);
        t.begin();
        t.list(1, 12, cols.len());
        for (c, &(off, len)) in cols.iter().zip(&chunks_meta) {
            t.begin();
            t.i64(2, off as i64);
            t.begin_field(3);
            t.i32(1, c.ty);
            t.list(2, 5, 2);
            t.zigzag(0);
            t.zigzag(3);
            t.list(3, 8, 1);
            t.bytes(c.name.as_bytes());
            t.i32(4, 0); // UNCOMPRESSED
            t.i64(5, nrows as i64);
            t.i64(6, len as i64);
            t.i64(7, len as i64);
            t.i64(9, off as i64);
            t.end();
            t.end();
        }
        t.i64(2, chunks_meta.iter().map(|m| m.1 as i64).sum());
        t.i64(3, nrows as i64);
        t.end();
    }
    t.binary(6, b"shopping-sessions");
    t.b.push(0);
    let footer_len = (t.b.len() as u32).to_le_bytes();
    let mut bufs: Vec<&[u8]> = Vec::with_capacity(headers.len() * 3 + 4);
    bufs.push(b"PAR1");
    let mut h = headers.iter();
    for col in pages {
        for p in col {
            bufs.push(h.next().unwrap());
            if !p.body[0].is_empty() { bufs.push(p.body[0]); }
            if !p.body[1].is_empty() { bufs.push(p.body[1]); }
        }
    }
    bufs.push(&t.b);
    bufs.push(&footer_len);
    bufs.push(b"PAR1");
    write_all_slices(&mut File::create(path).unwrap(), &bufs);
}

#[inline(always)]
fn put_str(v: &mut Vec<u8>, s: &[u8]) {
    v.extend_from_slice(&(s.len() as u32).to_le_bytes());
    v.extend_from_slice(s);
}

/// The events of one parsed chunk in one exactly sized block, sorted by dedup bucket:
/// bucket b is `offs[b] .. offs[b + 1]`.
struct ChunkOut { base: *mut Ev, block: Vec<Ev>, offs: Vec<u32> }
unsafe impl Send for ChunkOut {}
unsafe impl Sync for ChunkOut {}
impl ChunkOut {
    /// Appends bucket `b` as (pointer, length) unless it is empty.
    #[inline(always)]
    fn pieces(&self, b: usize, out: &mut Vec<(*mut Ev, usize)>) {
        let (lo, hi) = (self.offs[b] as usize, self.offs[b + 1] as usize);
        if hi > lo { out.push((unsafe { self.base.add(lo) }, hi - lo)); }
    }
}
thread_local! {
    /// Per-thread staging for one chunk's events and their bucket numbers, reused chunk after chunk.
    static STAGE: std::cell::RefCell<(Vec<Ev>, Vec<u16>)> = const { std::cell::RefCell::new((Vec::new(), Vec::new())) };
}

/// True when the CPU has what the fast parsers are compiled for (and SS_BASELINE is not set).
fn fast_cpu() -> bool {
    #[cfg(target_arch = "x86_64")]
    {
        return std::env::var_os("SS_BASELINE").is_none()
            && is_x86_feature_detected!("avx2") && is_x86_feature_detected!("bmi1")
            && is_x86_feature_detected!("bmi2") && is_x86_feature_detected!("popcnt");
    }
    #[allow(unreachable_code)]
    false
}
#[inline(always)]
fn pbucket(pk: u64, np_mask: u64) -> usize { ((pk >> 40) & np_mask) as usize }

struct EvCtx<'a> { nb: usize, nb_shift: u32, ws: i64, we: i64, products: &'a IdMap<u32> }
/// Parses one chunk of an events file into a block sorted by dedup bucket.
#[inline(always)]
fn parse_events<const WIDE: bool>(part: &[u8], c: &EvCtx) -> ChunkOut {
    // Stage the chunk's events in arrival order, counting per bucket, then place them in a block
    // of exactly the right size. Nothing is reserved that is not used.
    let (nb, nb_shift, ws, we) = (c.nb, c.nb_shift, c.ws, c.we);
    // one chunk at a time per thread, and nothing below re-enters this function
    let (staged, buckets) = unsafe { &mut *STAGE.with(|s| s.as_ptr()) };
    staged.clear();
    buckets.clear();
    let mut offs = vec![0u32; nb + 1];
    let mut dc = DateCache::new();
    scan_lines::<7, WIDE>(part, |[id, user, ts, ingest, ty, product, price]| {
        if id.is_empty() { return; }
        let h = xxh3_128(id);
        let hi = (h >> 64) as u64;
        let ingest_ms = parse_ts(ingest, &mut dc);
        let mut e = Ev { eid: h as u64, user: 0, name: 0, tp: DEAD_TP, ingest: i32::MIN, cat: 0, eid2: hi as u16 };
        if let Some(ing) = ingest_ms {
            e.ingest = ((ing - ws).div_euclid(1000)).clamp(i32::MIN as i64 + 1, i32::MAX as i64) as i32;
        }
        (|| {
            if user.is_empty() || product.is_empty() { return; }
            let Some(t) = parse_ts(ts, &mut dc) else { return };
            if t < ws || t >= we { return; }
            let Some(ing) = ingest_ms else { return };
            if ing - t > DAY_MS { return; }
            let mut cents = 0u32;
            match ty {
                b"view" | b"cart" => {}
                b"purchase" => {
                    let Some(p) = parse_price(price) else { return };
                    cents = p;
                    e.cat = c.products.get(&xxh3_64(product)).copied().unwrap_or(0) as u16;
                }
                _ => return,
            }
            e.user = xxh3_64(user);
            e.name = pack(user);
            e.tp = (((t - ws) as u64) << PRICE_BITS) | cents as u64;
        })();
        let b = (hi >> nb_shift) as usize;
        unsafe { *offs.get_unchecked_mut(b + 1) += 1; }
        staged.push(e);
        buckets.push(b as u16);
    });
    for b in 0..nb { offs[b + 1] += offs[b]; }
    let n = staged.len();
    let mut block: Vec<Ev> = Vec::with_capacity(n.max(1));
    advise_huge(&block);
    let base = block.as_mut_ptr();
    let mut next: Vec<u32> = offs[..nb].to_vec();
    for (e, &b) in staged.iter().zip(buckets.iter()) {
        unsafe {
            let slot = next.get_unchecked_mut(b as usize);
            base.add(*slot as usize).write(*e);
            *slot += 1;
        }
    }
    unsafe { block.set_len(n); }
    ChunkOut { base, block, offs }
}
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2,bmi1,bmi2,popcnt")]
unsafe fn parse_events_fast(part: &[u8], c: &EvCtx) -> ChunkOut { parse_events::<true>(part, c) }

struct CkCtx<'a> { ws: i64, we: i64, campaigns: &'a IdMap<u32>, camp_names: &'a [&'a [u8]], links: &'a LinkTab, np: usize, np_mask: u64 }
/// Parses one chunk of a clicks file: the valid clicks with their person, and how many fall in
/// each person partition.
#[inline(always)]
fn parse_clicks<const WIDE: bool>(part: &[u8], c: &CkCtx) -> (Vec<Ck>, Vec<u32>) {
    let (ws, we) = (c.ws, c.we);
    let mut v: Vec<Ck> = Vec::with_capacity(part.len() / 40 + 4);
    let mut dc = DateCache::new();
    scan_lines::<4, WIDE>(part, |[id, user, camp, ts]| {
        if id.is_empty() || user.is_empty() { return; }
        let Some(t) = parse_ts(ts, &mut dc) else { return };
        if t < ws - WEEK_MS || t >= we { return; }
        let Some(&k) = c.campaigns.get(&xxh3_64(camp)) else { return };
        if c.camp_names[k as usize] != camp { return; }
        v.push(Ck { pk: xxh3_64(user), ts: t, id: pack(id), camp: k, pad: 0 });
    });
    let mut cnt = vec![0u32; c.np];
    for blk in v.chunks_mut(32) {
        for k in blk.iter() { prefetch(c.links.slot(k.pk)); }
        for k in blk.iter_mut() {
            k.pk = c.links.person(k.pk, 1).0;
            cnt[pbucket(k.pk, c.np_mask)] += 1;
        }
    }
    (v, cnt)
}
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2,bmi1,bmi2,popcnt")]
unsafe fn parse_clicks_fast(part: &[u8], c: &CkCtx) -> (Vec<Ck>, Vec<u32>) { parse_clicks::<true>(part, c) }

/// One person partition's user_daily rows, already PLAIN-encoded per column.
#[derive(Default)]
struct PartOut { rows: usize, user: Vec<u8>, day: Vec<u8>, sess: Vec<u8>, evs: Vec<u8>, rev: Vec<u8>, bits: Vec<u8>, def: Vec<u8>, top: Vec<u8> }

/// User and system CPU seconds of the whole process so far (for the stage log only).
fn cpu_seconds() -> (f64, f64) {
    #[cfg(unix)]
    unsafe {
        let mut u: libc::rusage = std::mem::zeroed();
        libc::getrusage(libc::RUSAGE_SELF, &mut u);
        return (u.ru_utime.tv_sec as f64 + u.ru_utime.tv_usec as f64 / 1e6, u.ru_stime.tv_sec as f64 + u.ru_stime.tv_usec as f64 / 1e6);
    }
    #[allow(unreachable_code)]
    (0.0, 0.0)
}

/// Cycles and instructions so far, where the OS offers them cheaply (macOS; development only).
fn cycles() -> String {
    #[cfg(target_os = "macos")]
    unsafe {
        let mut r: libc::rusage_info_v4 = std::mem::zeroed();
        if libc::proc_pid_rusage(libc::getpid(), libc::RUSAGE_INFO_V4, &mut r as *mut _ as *mut libc::rusage_info_t) == 0 {
            return format!(" Gcyc {:7.3} Ginstr {:7.3}", r.ri_cycles as f64 / 1e9, r.ri_instructions as f64 / 1e9);
        }
    }
    String::new()
}

struct PerThread<T>(Vec<UnsafeCell<T>>);
unsafe impl<T> Sync for PerThread<T> {}
impl<T> PerThread<T> {
    #[allow(clippy::mut_from_ref)]
    fn mine(&self) -> &mut T { unsafe { &mut *self.0[rayon::current_thread_index().unwrap()].get() } }
}

/// glibc's defaults hand big blocks straight back to the kernel and grow heaps in small steps,
/// which costs a system call and fresh page faults every time. Nothing here is long-lived enough
/// to be worth returning, so keep memory in the heap and grow it in large steps.
fn tune_allocator() {
    #[cfg(all(target_os = "linux", target_env = "gnu"))]
    unsafe {
        libc::mallopt(libc::M_MMAP_THRESHOLD, 32 << 20);
        libc::mallopt(libc::M_TRIM_THRESHOLD, i32::MAX);
        libc::mallopt(libc::M_TOP_PAD, 512 << 20);
    }
}
/// Asks for huge pages behind a large allocation (helps where the host only gives them on request).
fn advise_huge<T>(v: &Vec<T>) {
    #[cfg(target_os = "linux")]
    unsafe {
        let (start, len) = (v.as_ptr() as usize, v.capacity() * std::mem::size_of::<T>());
        let a = (start + 4095) & !4095;
        let b = (start + len) & !4095;
        if b > a + (4 << 20) { libc::madvise(a as *mut libc::c_void, b - a, libc::MADV_HUGEPAGE); }
    }
    #[cfg(not(target_os = "linux"))]
    let _ = v;
}

/// Returns the pages behind a buffer to the kernel now, from the calling thread, while keeping
/// the buffer itself valid (it reads as zeros afterwards).
fn release_pages<T>(v: &Vec<T>) {
    #[cfg(target_os = "linux")]
    unsafe {
        let (start, len) = (v.as_ptr() as usize, v.capacity() * std::mem::size_of::<T>());
        let a = (start + 4095) & !4095;
        let b = (start + len) & !4095;
        if b > a { libc::madvise(a as *mut libc::c_void, b - a, libc::MADV_DONTNEED); }
    }
    #[cfg(not(target_os = "linux"))]
    let _ = v;
}

fn main() {
    tune_allocator();
    let t0 = Instant::now();
    let data = PathBuf::from(std::env::var("DATA_DIR").unwrap_or_else(|_| "/data".into()));
    let out = PathBuf::from(std::env::var("OUTPUT_DIR").unwrap_or_else(|_| "/output".into()));
    let threads = std::env::var("NCPU").ok().and_then(|s| s.parse::<usize>().ok()).filter(|&n| n > 0)
        .unwrap_or_else(|| std::thread::available_parallelism().map(|n| n.get()).unwrap_or(8));
    rayon::ThreadPoolBuilder::new().num_threads(threads).build_global().unwrap();
    let lap = |what: &str| { let (u, k) = cpu_seconds(); eprintln!("[{:7.3}s user {:7.3}s sys {:7.3}s{}] {}", t0.elapsed().as_secs_f64(), u, k, cycles(), what) };

    let mf = std::fs::read_to_string(data.join("manifest.json")).expect("manifest.json");
    let ws = manifest_ts(&mf, "\"window_start\"");
    let we = manifest_ts(&mf, "\"window_end\"");
    let day0 = ws.div_euclid(DAY_MS);
    let ndays = ((we - 1).div_euclid(DAY_MS) - day0 + 1).max(1) as usize;

    // ---- links on a side thread: nothing needs them until the events are deduplicated
    let link_dir = data.join("links");
    let links_thread = std::thread::spawn(move || build_links(link_dir));

    // ---- products and campaigns
    let mut cats: Vec<&[u8]> = vec![b"unknown"];
    let mut cat_idx: HashMap<&[u8], u32> = HashMap::new();
    cat_idx.insert(b"unknown", 0);
    let mut products: IdMap<u32> = IdMap::default();
    let mut product_keys: HashMap<u64, &[u8]> = HashMap::new();
    let mut product_clash = false;
    if let Some(d) = map_file(&data.join("products.csv")) {
        for part in chunks(d, usize::MAX / 2) {
            let mut pos = 0;
            while pos < part.len() {
                let Some([p, c]) = split_line::<2>(part, &mut pos) else { continue };
                let next = cats.len() as u32;
                let ci = *cat_idx.entry(c).or_insert_with(|| { cats.push(c); next });
                let h = xxh3_64(p);
                if *product_keys.entry(h).or_insert(p) != p { product_clash = true; }
                products.entry(h).or_insert(ci);
            }
        }
    }
    assert!(!product_clash, "product hash clash");
    drop(product_keys);
    // rank of each category in byte order, for ties
    let mut order: Vec<u32> = (0..cats.len() as u32).collect();
    order.sort_by(|&a, &b| cats[a as usize].cmp(cats[b as usize]));
    let mut cat_rank = vec![0u32; cats.len()];
    for (r, &c) in order.iter().enumerate() { cat_rank[c as usize] = r as u32; }

    let mut camp_names: Vec<&[u8]> = vec![b"organic"];
    let mut camp_chan: Vec<&[u8]> = vec![b"organic"];
    let mut campaigns: IdMap<u32> = IdMap::default(); // by hash; lookups confirm the bytes
    let mut camp_seen: hashbrown::HashSet<&[u8]> = hashbrown::HashSet::new();
    if let Some(d) = map_file(&data.join("campaigns.csv")) {
        for part in chunks(d, usize::MAX / 2) {
            let mut pos = 0;
            while pos < part.len() {
                let Some([c, ch]) = split_line::<2>(part, &mut pos) else { continue };
                if c.is_empty() { continue; }
                let next = camp_names.len() as u32;
                if !camp_seen.insert(c) { continue; }
                let h = xxh3_64(c);
                assert!(!campaigns.contains_key(&h), "campaign hash clash");
                campaigns.insert(h, next);
                camp_names.push(c);
                camp_chan.push(ch);
            }
        }
    }
    let ncamp = camp_names.len();

    // ---- events: parse into buckets by event-id hash
    let ev_files = map_dir(&data.join("events"));
    let ev_bytes: usize = ev_files.iter().map(|d| d.len()).sum();
    let est_events = ev_bytes / 85 + 1;
    // SS_NB and SS_NP force the bucket and partition counts, to test a large-data layout on small data
    let knob = |k: &str| std::env::var(k).ok().and_then(|x| x.parse::<usize>().ok()).filter(|n| n.is_power_of_two() && *n >= 2 && *n <= 4096);
    let nb = knob("SS_NB").unwrap_or((est_events / 16_000).next_power_of_two().clamp(64, 4096)); // dedup buckets, sized to stay in cache
    let nb_shift = 64 - nb.trailing_zeros();
    let np = knob("SS_NP").unwrap_or((est_events / 20_000).next_power_of_two().clamp(16, 4096)); // person partitions
    assert!(we - ws < 1i64 << 40 && we >= ws, "window too long for the packed timestamp");
    assert!(cats.len() <= u16::MAX as usize, "too many categories for the packed record");
    let np_mask = (np - 1) as u64;
    let chunk = (ev_bytes / (threads * 8)).clamp(1 << 20, 16 << 20);
    let ev_parts: Vec<&'static [u8]> = ev_files.iter().flat_map(|d| chunks(d, chunk)).collect();
    let fast = fast_cpu();
    let ev_ctx = EvCtx { nb, nb_shift, ws, we, products: &products };
    let parsed: Vec<ChunkOut> = ev_parts.par_iter().map(|part| {
        #[cfg(target_arch = "x86_64")]
        if fast { return unsafe { parse_events_fast(part, &ev_ctx) }; }
        parse_events::<false>(part, &ev_ctx)
    }).collect();
    rayon::broadcast(|_| { let (a, b) = unsafe { &mut *STAGE.with(|s| s.as_ptr()) }; release_pages(a); release_pages(b); });
    lap(&format!("events parsed ({} dedup buckets, {} person partitions, {} parser)", nb, np, if fast { "AVX2" } else { "baseline" }));

    let links = links_thread.join().unwrap();
    lap(&format!("links ready: {} slots", links.slots.len()));

    // ---- dedup each bucket, resolve people, count survivors per person partition
    let groups = (threads * 8).min(nb);
    let per_group = nb / groups; // both are powers of two or nb is a multiple: nb >= 64 and threads*8 may not divide
    let groups = nb.div_ceil(per_group);
    let counts: Vec<Vec<u32>> = (0..groups).into_par_iter().map(|g| {
        let mut cnt = vec![0u32; np];
        let mut table: Vec<u64> = Vec::new();
        let mut refs: Vec<*mut Ev> = Vec::new();
        let mut lists: Vec<(*mut Ev, usize)> = Vec::new();
        for b in (g * per_group)..((g + 1) * per_group).min(nb) {
            // this group is the only one touching bucket b of every chunk
            lists.clear();
            for c in &parsed { c.pieces(b, &mut lists); }
            let n: usize = lists.iter().map(|l| l.1).sum();
            if n == 0 { continue; }
            let cap = (n * 2).next_power_of_two();
            let mask = cap - 1;
            table.clear();
            table.resize(cap, 0);
            refs.clear();
            for &(ptr, len) in &lists {
                for e in unsafe { std::slice::from_raw_parts_mut(ptr, len) } {
                    let i = refs.len() as u64 + 1;
                    let tag = e.eid >> 32;
                    let mut s = e.eid as usize & mask;
                    loop {
                        let t = table[s];
                        if t == 0 { table[s] = (tag << 32) | i; break; }
                        if t >> 32 == tag {
                            let o = unsafe { &mut *refs[(t as u32 - 1) as usize] };
                            if o.eid == e.eid && o.eid2 == e.eid2 {
                                if e.ingest < o.ingest { o.tp = DEAD_TP; table[s] = (tag << 32) | i; } else { e.tp = DEAD_TP; }
                                break;
                            }
                        }
                        s = (s + 1) & mask;
                    }
                    refs.push(e as *mut Ev);
                }
            }
            // resolve the survivors to people, a block at a time so the table probes can be prefetched
            for blk in refs.chunks(32) {
                for &r in blk { let e = unsafe { &*r }; if e.tp != DEAD_TP { prefetch(links.slot(e.user)); } }
                for &r in blk {
                    let e = unsafe { &mut *r };
                    if e.tp == DEAD_TP { continue; }
                    let (pk, name) = links.person(e.user, e.name);
                    e.user = pk;
                    e.name = name;
                    cnt[pbucket(pk, np_mask)] += 1;
                }
            }
        }
        cnt
    }).collect();

    // ---- scatter survivors into one array, grouped by person partition
    let scatter_offsets = |counts: &Vec<Vec<u32>>| -> (Vec<usize>, Vec<Vec<usize>>) {
        let mut base = vec![0usize; np + 1];
        for c in counts { for p in 0..np { base[p + 1] += c[p] as usize; } }
        for p in 0..np { base[p + 1] += base[p]; }
        let mut run = base.clone();
        let offs = counts.iter().map(|c| {
            let o: Vec<usize> = run[..np].to_vec();
            for p in 0..np { run[p] += c[p] as usize; }
            o
        }).collect();
        (base, offs)
    };
    let (ev_base, ev_offs) = scatter_offsets(&counts);
    let total_ev = ev_base[np];
    let mut evs: Vec<Sv> = Vec::with_capacity(total_ev);
    advise_huge(&evs);
    note_vec(&evs);
    unsafe { evs.set_len(total_ev); }
    let evs_ptr = Raw(evs.as_mut_ptr());
    ev_offs.into_par_iter().enumerate().for_each(|(g, mut off)| {
        let mut lists: Vec<(*mut Ev, usize)> = Vec::new();
        for b in (g * per_group)..((g + 1) * per_group).min(nb) {
            lists.clear();
            for c in &parsed { c.pieces(b, &mut lists); }
            for &(ptr, len) in &lists {
                for e in unsafe { std::slice::from_raw_parts(ptr as *const Ev, len) } {
                    if e.tp == DEAD_TP { continue; }
                    let p = pbucket(e.user, np_mask);
                    let (ts, price) = (ws + (e.tp >> PRICE_BITS) as i64, (e.tp & ((1 << PRICE_BITS) - 1)) as u32);
                    unsafe { evs_ptr.get().add(off[p]).write(Sv { pk: e.user, ts, name: e.name, price, cat: e.cat as u32 }); }
                    off[p] += 1;
                }
            }
        }
    });
    // Give the blocks' pages back on all threads now; left for exit they are torn down by one.
    parsed.into_par_iter().for_each(|c| { release_pages(&c.block); drop(c); });
    lap(&format!("events deduped: {} survive", total_ev));

    // ---- clicks: parse, validate, resolve people; copies are identical, so dedup happens after the sort
    let ck_files = map_dir(&data.join("clicks"));
    let ck_bytes: usize = ck_files.iter().map(|d| d.len()).sum();
    let ck_chunk = (ck_bytes / (threads * 8)).clamp(1 << 20, 16 << 20);
    let ck_parts: Vec<&'static [u8]> = ck_files.iter().flat_map(|d| chunks(d, ck_chunk)).collect();
    let ck_ctx = CkCtx { ws, we, campaigns: &campaigns, camp_names: &camp_names, links: &links, np, np_mask };
    let ck_parsed: Vec<(Vec<Ck>, Vec<u32>)> = ck_parts.par_iter().map(|part| {
        #[cfg(target_arch = "x86_64")]
        if fast { return unsafe { parse_clicks_fast(part, &ck_ctx) }; }
        parse_clicks::<false>(part, &ck_ctx)
    }).collect();
    let ck_counts: Vec<Vec<u32>> = ck_parsed.iter().map(|x| x.1.clone()).collect();
    let (ck_base, ck_offs) = scatter_offsets(&ck_counts);
    let total_ck = ck_base[np];
    let mut cks: Vec<Ck> = Vec::with_capacity(total_ck);
    advise_huge(&cks);
    note_vec(&cks);
    unsafe { cks.set_len(total_ck); }
    let cks_ptr = Raw(cks.as_mut_ptr());
    ck_parsed.par_iter().zip(ck_offs.into_par_iter()).for_each(|((v, _), mut off)| {
        for c in v {
            let p = pbucket(c.pk, np_mask);
            unsafe { cks_ptr.get().add(off[p]).write(*c); }
            off[p] += 1;
        }
    });
    ck_parsed.into_par_iter().for_each(|(v, _)| { release_pages(&v); drop(v); });
    lap(&format!("clicks parsed: {} valid", total_ck));

    // ---- per partition: sort, sessionize, credit, assists, user_daily pages
    let camp_acc: PerThread<Vec<[i64; 4]>> = PerThread((0..threads).map(|_| UnsafeCell::new(vec![[0i64; 4]; ncamp * ndays])).collect());
    // Largest partitions first, one task each: a whale person is a long single-threaded job, and
    // started last it would leave the other threads idle at the end.
    let mut order: Vec<usize> = (0..np).collect();
    order.sort_unstable_by_key(|&b| std::cmp::Reverse(ev_base[b + 1] - ev_base[b]));
    let parts: Vec<PartOut> = order.par_iter().with_max_len(1).map(|&b| {
        let ev: &mut [Sv] = unsafe { std::slice::from_raw_parts_mut(evs_ptr.get().add(ev_base[b]), ev_base[b + 1] - ev_base[b]) };
        let ck_all: &mut [Ck] = unsafe { std::slice::from_raw_parts_mut(cks_ptr.get().add(ck_base[b]), ck_base[b + 1] - ck_base[b]) };
        // each rayon worker owns one accumulator
        let camp: &mut Vec<[i64; 4]> = camp_acc.mine();
        let mut p = PartOut::default();
        if ev.is_empty() { return p; }
        // Group by person without a full sort: number the people with a small table, counting-sort
        // the events and clicks by that number, then sort each person's few rows by time.
        let n = ev.len();
        let cap = (n + n / 2 + 1).next_power_of_two();
        let shift = 64 - cap.trailing_zeros();
        let mut t_pk: Vec<u64> = vec![0; cap];
        let mut t_id: Vec<u32> = vec![u32::MAX; cap];
        let mut ev_id: Vec<u32> = Vec::with_capacity(n);
        let mut e_off: Vec<u32> = Vec::new(); // events per person, then offsets
        for e in ev.iter() {
            let mut s = (e.pk.wrapping_mul(0x9E37_79B9_7F4A_7C15) >> shift) as usize;
            let id = loop {
                let id = t_id[s];
                if id == u32::MAX {
                    let id = e_off.len() as u32;
                    t_pk[s] = e.pk;
                    t_id[s] = id;
                    e_off.push(0);
                    break id;
                }
                if t_pk[s] == e.pk { break id; }
                s = (s + 1) & (cap - 1);
            };
            e_off[id as usize] += 1;
            ev_id.push(id);
        }
        let people = e_off.len();
        let mut ck_id: Vec<u32> = Vec::with_capacity(ck_all.len());
        let mut c_off: Vec<u32> = vec![0; people + 1];
        for c in ck_all.iter() {
            let mut s = (c.pk.wrapping_mul(0x9E37_79B9_7F4A_7C15) >> shift) as usize;
            let id = loop {
                let id = t_id[s];
                if id == u32::MAX || t_pk[s] == c.pk { break id; } // MAX: a person with no events
                s = (s + 1) & (cap - 1);
            };
            if id != u32::MAX { c_off[id as usize] += 1; }
            ck_id.push(id);
        }
        // counts -> start offsets (one extra slot at the end)
        e_off.push(0);
        let (mut ea, mut ca) = (0u32, 0u32);
        for k in 0..=people {
            let (x, y) = (e_off[k], c_off[k]);
            e_off[k] = ea;
            c_off[k] = ca;
            ea += x;
            ca += y;
        }
        let mut evs_sorted: Vec<Sv> = Vec::with_capacity(n);
        let mut cks_sorted: Vec<Ck> = Vec::with_capacity(ca as usize);
        unsafe {
            evs_sorted.set_len(n);
            cks_sorted.set_len(ca as usize);
            let mut next: Vec<u32> = e_off[..people].to_vec();
            for (e, &id) in ev.iter().zip(&ev_id) {
                let slot = next.get_unchecked_mut(id as usize);
                *evs_sorted.get_unchecked_mut(*slot as usize) = *e;
                *slot += 1;
            }
            next.copy_from_slice(&c_off[..people]);
            for (c, &id) in ck_all.iter().zip(&ck_id) {
                if id == u32::MAX { continue; }
                let slot = next.get_unchecked_mut(id as usize);
                *cks_sorted.get_unchecked_mut(*slot as usize) = *c;
                *slot += 1;
            }
        }
        drop((t_pk, t_id, ev_id, ck_id));
        let ev: &mut [Sv] = &mut evs_sorted;

        let guess = ev.len() / 4 + 16;
        p.user.reserve(guess * 16); p.day.reserve(guess * 4); p.sess.reserve(guess * 4); p.evs.reserve(guess * 4); p.rev.reserve(guess * 8);
        let mut cat_sum = vec![0i64; cats.len()];
        let mut touched: Vec<u32> = Vec::new();
        let mut starts: Vec<i64> = Vec::new();       // this person's session starts
        let mut runs: Vec<(usize, usize)> = Vec::new(); // (day index, first session index) per day
        let mut ct: Vec<(u32, i64)> = Vec::new();
        // Time order through 64-bit keys, so the 32-byte records never move: time since the
        // window start (40 bits), the record's index within the person (23 bits), and whether it
        // is a purchase (1 bit). A person with 2^23 events or more is sorted the plain way.
        const KEY_INDEX_BITS: u32 = 23;
        const CLICK_INDEX_BITS: u32 = 22;
        let click_base = ws - WEEK_MS; // the earliest valid click time
        let mut keys: Vec<u64> = Vec::new();
        let mut pc: Vec<(i64, u32, u64)> = Vec::new();
        let mut ckeys: Vec<u64> = Vec::new();
        for person in 0..people {
            let (i, j) = (e_off[person] as usize, e_off[person + 1] as usize);
            // the name's bytes are in a mapped file, far from anything in cache: ask for them early
            if person + 3 < people { prefetch((ev[e_off[person + 3] as usize].name & 0xFFFF_FFFF_FFFF) as *const u8); }
            let keyed = j - i < (1 << KEY_INDEX_BITS);
            if keyed {
                keys.clear();
                keys.extend(ev[i..j].iter().enumerate().map(|(x, e)| (((e.ts - ws) as u64) << (KEY_INDEX_BITS + 1)) | ((x as u64) << 1) | (e.price > 0) as u64));
                keys.sort_unstable();
            } else {
                ev[i..j].sort_unstable_by_key(|e| e.ts);
            }
            // the k-th event of this person in time order: its time, and its record if it is a purchase
            let at = |k: usize| -> (i64, Option<&Sv>) {
                if keyed {
                    let key = unsafe { *keys.get_unchecked(k - i) };
                    let rec = if key & 1 != 0 { Some(unsafe { ev.get_unchecked(i + ((key >> 1) & ((1 << KEY_INDEX_BITS) - 1)) as usize) }) } else { None };
                    (ws + (key >> (KEY_INDEX_BITS + 1)) as i64, rec)
                } else {
                    let e = &ev[k];
                    (e.ts, if e.price > 0 { Some(e) } else { None })
                }
            };
            // This person's clicks as (time, campaign) in time order, and among clicks at the same
            // millisecond the one with the byte-wise smallest click_id last: that is the one a
            // session starting then is credited to. Copies of a click are left in: they carry the
            // same time and campaign, so they change neither the credit nor the assists.
            let pc_all = &mut cks_sorted[c_off[person] as usize..c_off[person + 1] as usize];
            pc.clear();
            if pc_all.len() < (1 << CLICK_INDEX_BITS) {
                ckeys.clear();
                ckeys.extend(pc_all.iter().enumerate().map(|(x, c)| (((c.ts - click_base) as u64) << CLICK_INDEX_BITS) | x as u64));
                ckeys.sort_unstable();
                let mut run = 0usize; // where the current run of equal times starts in `pc`
                for (pos, &key) in ckeys.iter().enumerate() {
                    let c = &pc_all[(key & ((1 << CLICK_INDEX_BITS) - 1)) as usize];
                    if pos > 0 && pc[pos - 1].0 != c.ts { run = pos; }
                    pc.push((c.ts, c.camp, c.id));
                    // keep the smallest id of the run at its end
                    if pos > run && unpack(pc[pos].2) > unpack(pc[pos - 1].2) { pc.swap(pos, pos - 1); }
                }
            } else {
                pc_all.sort_unstable_by(|x, y| x.ts.cmp(&y.ts).then_with(|| if x.id == y.id { std::cmp::Ordering::Equal } else { unpack(y.id).cmp(unpack(x.id)) }));
                pc.extend(pc_all.iter().map(|c| (c.ts, c.camp, c.id)));
            }
            let pc: &[(i64, u32, u64)] = &pc;
            starts.clear(); runs.clear();

            let name = unpack(ev[i].name);
            let mut k = i;
            let mut cptr = 0usize; // clicks with ts <= current session start
            let (mut cur_day, mut d_sessions, mut d_events, mut d_rev) = (usize::MAX, 0i64, 0i64, 0i64);
            let flush = |p: &mut PartOut, day: usize, s: i64, e: i64, r: i64, cat_sum: &mut Vec<i64>, touched: &mut Vec<u32>| {
                let mut best = NO_CAT;
                for &c in touched.iter() {
                    if best == NO_CAT || cat_sum[c as usize] > cat_sum[best as usize]
                        || (cat_sum[c as usize] == cat_sum[best as usize] && cat_rank[c as usize] < cat_rank[best as usize]) {
                        best = c;
                    }
                }
                for &c in touched.iter() { cat_sum[c as usize] = 0; }
                touched.clear();
                put_str(&mut p.user, name);
                p.day.extend_from_slice(&((day0 + day as i64) as i32).to_le_bytes());
                p.sess.extend_from_slice(&(s as i32).to_le_bytes());
                p.evs.extend_from_slice(&(e as i32).to_le_bytes());
                p.rev.extend_from_slice(&r.to_le_bytes());
                if p.rows % 8 == 0 { p.bits.push(0); }
                if best != NO_CAT {
                    *p.bits.last_mut().unwrap() |= 1 << (p.rows % 8);
                    put_str(&mut p.top, cats[best as usize]);
                }
                p.rows += 1;
            };
            while k < j {
                let start = at(k).0;
                let day = (start.div_euclid(DAY_MS) - day0) as usize;
                if day != cur_day {
                    if cur_day != usize::MAX { flush(&mut p, cur_day, d_sessions, d_events, d_rev, &mut cat_sum, &mut touched); }
                    cur_day = day; d_sessions = 0; d_events = 0; d_rev = 0;
                    runs.push((day, starts.len()));
                }
                let (mut n, mut rev, mut prev) = (0i64, 0i64, start);
                while k < j {
                    let (ts, purchase) = at(k);
                    if ts - prev > GAP_MS { break; }
                    if let Some(e) = purchase {
                        rev += e.price as i64;
                        if cat_sum[e.cat as usize] == 0 { touched.push(e.cat); }
                        cat_sum[e.cat as usize] += e.price as i64;
                    }
                    n += 1; prev = ts; k += 1;
                }
                d_sessions += 1; d_events += n; d_rev += rev;
                starts.push(start);
                while cptr < pc.len() && pc[cptr].0 <= start { cptr += 1; }
                let c = if cptr > 0 && start - pc[cptr - 1].0 <= WEEK_MS { pc[cptr - 1].1 as usize } else { 0 };
                let cell = &mut camp[c * ndays + day];
                cell[0] += 1; cell[1] += (rev > 0) as i64; cell[2] += rev;
            }
            flush(&mut p, cur_day, d_sessions, d_events, d_rev, &mut cat_sum, &mut touched);

            // assists: per campaign, merge the [click, click + 7 days] spans and count the sessions inside, by day
            if !pc.is_empty() {
                ct.clear();
                ct.extend(pc.iter().map(|c| (c.1, c.0)));
                ct.sort_unstable();
                let mut a = 0;
                while a < ct.len() {
                    let (cid, lo) = ct[a];
                    let mut hi = lo + WEEK_MS;
                    a += 1;
                    while a < ct.len() && ct[a].0 == cid && ct[a].1 <= hi { hi = ct[a].1 + WEEK_MS; a += 1; }
                    let i0 = starts.partition_point(|&s| s < lo);
                    let i1 = starts.partition_point(|&s| s <= hi);
                    if i0 >= i1 { continue; }
                    for (r, &(day, first)) in runs.iter().enumerate() {
                        let end = if r + 1 < runs.len() { runs[r + 1].1 } else { starts.len() };
                        let (x, y) = (first.max(i0), end.min(i1));
                        if x < y { camp[cid as usize * ndays + day][3] += (y - x) as i64; }
                    }
                }
            }
        }
        // definition levels of top_category: one bit-packed run, behind its 4-byte length
        let mut runs_hdr = Thrift::new();
        runs_hdr.varint(((p.bits.len() as u64) << 1) | 1);
        p.def.extend_from_slice(&((runs_hdr.b.len() + p.bits.len()) as u32).to_le_bytes());
        p.def.extend_from_slice(&runs_hdr.b);
        p.def.extend_from_slice(&p.bits);
        p
    }).collect();
    lap("sessions, credit and assists done");

    // ---- write
    std::fs::create_dir_all(out.join("user_daily")).unwrap();
    std::fs::create_dir_all(out.join("campaign_daily")).unwrap();
    let ucols = [
        Col { name: "user_id", ty: T_BYTES, utf8: true, date: false, optional: false },
        Col { name: "day", ty: T_INT32, utf8: false, date: true, optional: false },
        Col { name: "sessions", ty: T_INT32, utf8: false, date: false, optional: false },
        Col { name: "events", ty: T_INT32, utf8: false, date: false, optional: false },
        Col { name: "revenue_cents", ty: T_INT64, utf8: false, date: false, optional: false },
        Col { name: "top_category", ty: T_BYTES, utf8: true, date: false, optional: true },
    ];
    let files = (threads * 2).min(np);
    let per = np.div_ceil(files);
    let none: &[u8] = &[];
    (0..files).into_par_iter().for_each(|g| {
        let ps: Vec<&PartOut> = parts[(g * per).min(np)..((g + 1) * per).min(np)].iter().filter(|p| p.rows > 0).collect();
        let rows: usize = ps.iter().map(|p| p.rows).sum();
        if rows == 0 && g > 0 { return; }
        let pages: Vec<Vec<Page>> = vec![
            ps.iter().map(|p| Page { nvals: p.rows, body: [&p.user, none] }).collect(),
            ps.iter().map(|p| Page { nvals: p.rows, body: [&p.day, none] }).collect(),
            ps.iter().map(|p| Page { nvals: p.rows, body: [&p.sess, none] }).collect(),
            ps.iter().map(|p| Page { nvals: p.rows, body: [&p.evs, none] }).collect(),
            ps.iter().map(|p| Page { nvals: p.rows, body: [&p.rev, none] }).collect(),
            ps.iter().map(|p| Page { nvals: p.rows, body: [&p.def, &p.top] }).collect(),
        ];
        write_parquet(&out.join("user_daily").join(format!("part-{g:03}.parquet")), &ucols, rows, &pages);
    });

    let mut camp = vec![[0i64; 4]; ncamp * ndays];
    for cell in camp_acc.0 { for (a, b) in camp.iter_mut().zip(cell.into_inner()) { for q in 0..4 { a[q] += b[q]; } } }
    let (mut cid, mut chan, mut cday) = (Vec::new(), Vec::new(), Vec::new());
    let mut c4: [Vec<u8>; 4] = Default::default();
    let mut crows = 0usize;
    for c in 0..ncamp { for d in 0..ndays {
        let v = camp[c * ndays + d];
        if v[0] == 0 && v[3] == 0 { continue; }
        put_str(&mut cid, camp_names[c]);
        put_str(&mut chan, camp_chan[c]);
        cday.extend_from_slice(&((day0 + d as i64) as i32).to_le_bytes());
        for q in 0..4 { c4[q].extend_from_slice(&v[q].to_le_bytes()); }
        crows += 1;
    } }
    let ccols = [
        Col { name: "campaign_id", ty: T_BYTES, utf8: true, date: false, optional: false },
        Col { name: "channel", ty: T_BYTES, utf8: true, date: false, optional: false },
        Col { name: "day", ty: T_INT32, utf8: false, date: true, optional: false },
        Col { name: "sessions", ty: T_INT64, utf8: false, date: false, optional: false },
        Col { name: "purchasing_sessions", ty: T_INT64, utf8: false, date: false, optional: false },
        Col { name: "revenue_cents", ty: T_INT64, utf8: false, date: false, optional: false },
        Col { name: "assisted_sessions", ty: T_INT64, utf8: false, date: false, optional: false },
    ];
    let bufs: [&[u8]; 7] = [&cid, &chan, &cday, &c4[0], &c4[1], &c4[2], &c4[3]];
    let cpages: Vec<Vec<Page>> = bufs.iter().map(|b| if crows == 0 { vec![] } else { vec![Page { nvals: crows, body: [b, none] }] }).collect();
    write_parquet(&out.join("campaign_daily").join("part-000.parquet"), &ccols, crows, &cpages);
    lap("written");
    release_regions();
    lap("released");
    // Skip destructors and exit handlers: the OS frees the rest.
    #[cfg(unix)]
    unsafe { libc::_exit(0) }
    #[allow(unreachable_code)]
    std::process::exit(0);
}
