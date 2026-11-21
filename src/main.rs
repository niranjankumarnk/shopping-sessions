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
use std::io::Write;
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
const DEAD: i64 = i64::MIN;
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
struct Ev { eid: u64, user: u64, name: u64, ts: i64, eid2: u32, ingest: i32, price: u32, cat: u32 }
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

/// Two bit masks for one block of bytes: the field and line ends (`,` and `\n`), and the quotes.
/// Bit `i << MASK_SHIFT` is byte i.
#[cfg(target_arch = "x86_64")]
const BLOCK: usize = 64;
#[cfg(target_arch = "x86_64")]
const MASK_SHIFT: u32 = 0;
#[cfg(target_arch = "x86_64")]
#[inline(always)]
unsafe fn delim_masks(p: *const u8) -> (u64, u64) {
    use core::arch::x86_64::*; // SSE2 is part of every x86-64 CPU
    let (c, n, q) = (_mm_set1_epi8(b',' as i8), _mm_set1_epi8(b'\n' as i8), _mm_set1_epi8(b'"' as i8));
    let (mut dm, mut qm) = (0u64, 0u64);
    for k in 0..4 {
        let v = _mm_loadu_si128(p.add(k * 16) as *const __m128i);
        let d = _mm_or_si128(_mm_cmpeq_epi8(v, c), _mm_cmpeq_epi8(v, n));
        dm |= (_mm_movemask_epi8(d) as u32 as u64) << (k * 16);
        qm |= (_mm_movemask_epi8(_mm_cmpeq_epi8(v, q)) as u32 as u64) << (k * 16);
    }
    (dm, qm)
}
#[cfg(target_arch = "aarch64")]
const BLOCK: usize = 16;
#[cfg(target_arch = "aarch64")]
const MASK_SHIFT: u32 = 2;
#[cfg(target_arch = "aarch64")]
#[inline(always)]
unsafe fn delim_masks(p: *const u8) -> (u64, u64) {
    use core::arch::aarch64::*;
    let v = vld1q_u8(p);
    let d = vorrq_u8(vceqq_u8(v, vdupq_n_u8(b',')), vceqq_u8(v, vdupq_n_u8(b'\n')));
    let q = vceqq_u8(v, vdupq_n_u8(b'"'));
    // 4 bits per byte; keep one of them
    let nib = |x: uint8x16_t| vget_lane_u64::<0>(vreinterpret_u64_u8(vshrn_n_u16::<4>(vreinterpretq_u16_u8(x)))) & 0x8888_8888_8888_8888;
    (nib(d), nib(q))
}
#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
const BLOCK: usize = usize::MAX / 2;
#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
const MASK_SHIFT: u32 = 0;
#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
#[inline(always)]
unsafe fn delim_masks(_: *const u8) -> (u64, u64) { (0, 0) }

/// Calls `f` with the N fields of every well-formed line of `data`, whole-field quotes stripped.
/// Same rules as `split_line`. Only commas and newlines are visited one by one; quotes are counted
/// per line, and a line is well formed when every quote is the first or last byte of a field that
/// both starts and ends with one: quotes in the line == 2 x such fields.
#[inline(always)]
#[allow(unused_assignments)]
fn scan_lines<'a, const N: usize>(data: &'a [u8], mut f: impl FnMut([&'a [u8]; N])) {
    let len = data.len();
    let ptr = data.as_ptr();
    let mut cuts = [0usize; 9];
    assert!(N <= 8);
    let (mut n, mut line, mut qtot, mut qstart) = (0usize, 0usize, 0usize, 0usize);
    macro_rules! line_end {
        ($i:expr, $quotes:expr) => {{
            let i: usize = $i;
            let quotes: usize = $quotes;
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
        }};
    }
    let mut pos = 0usize;
    while pos + BLOCK <= len {
        let (mut m, qm) = unsafe { delim_masks(ptr.add(pos)) };
        while m != 0 {
            let t = m.trailing_zeros();
            let i = pos + (t >> MASK_SHIFT) as usize;
            if unsafe { *ptr.add(i) } == b',' {
                unsafe { *cuts.get_unchecked_mut(n) = i; }
                n = (n + 1).min(N);
            } else {
                let seen = qtot + (qm & ((1u64 << t) - 1)).count_ones() as usize;
                line_end!(i, seen - qstart);
                qstart = seen;
            }
            m &= m - 1;
        }
        qtot += qm.count_ones() as usize;
        pos += BLOCK;
    }
    while pos < len {
        let c = unsafe { *ptr.add(pos) };
        if c == b',' {
            cuts[n] = pos;
            n = (n + 1).min(N);
        } else if c == b'"' {
            qtot += 1;
        } else if c == b'\n' {
            line_end!(pos, qtot - qstart);
            qstart = qtot;
        }
        pos += 1;
    }
    if line < len { line_end!(len, qtot - qstart); }
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

/// Epoch milliseconds, or None for a bad timestamp (window not checked here).
#[inline(always)]
fn parse_ts(s: &[u8]) -> Option<i64> {
    let n = s.len();
    if (n == 20 || n == 25) && s[4] == b'-' {
        // YYYY-MM- | DDTHH:MM | then H:MM:SSZ (F1) or SS+HH:MM after a ':' (F2)
        let t0 = ld8(s, 0) ^ le([b'0', b'0', b'0', b'0', b'-', b'0', b'0', b'-']);
        let t1 = ld8(s, 8) ^ le([b'0', b'0', b'T', b'0', b'0', b':', b'0', b'0']);
        let mut ok = ok8(t0, le([DIG, DIG, DIG, DIG, SEP, DIG, DIG, SEP])) & ok8(t1, le([DIG, DIG, SEP, DIG, DIG, SEP, DIG, DIG]));
        let (p0, p1) = (pairs(t0), pairs(t1));
        let (cc, yy, mo) = (byte(p0, 0), byte(p0, 2), byte(p0, 5));
        let (d, h, mi) = (byte(p1, 0), byte(p1, 3), byte(p1, 6));
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
        let leap = if yy != 0 { yy & 3 == 0 } else { cc & 3 == 0 };
        let dim = DIM[(mo & 15) as usize] + ((mo == 2) & leap) as i64;
        ok &= (mo >= 1) & (mo <= 12) & (d >= 1) & (d <= dim) & (h <= 23) & (mi <= 59) & (se <= 59);
        if !ok { return None; }
        let secs = days_from_civil(cc * 100 + yy, mo, d) * 86400 + h * 3600 + mi * 60 + se;
        return Some((secs - off) * 1000);
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
            let (a, b) = (parse_ts(&s), parse_ts_ref(&s));
            assert_eq!(a, b, "{:?}", String::from_utf8_lossy(&s));
            checked += 1;
            valid += a.is_some() as u64;
        }
        assert!(valid > checked / 4 && valid < checked);
        for s in [&b""[..], b"2028-02-29T00:00:00Z", b"2027-02-29T00:00:00Z", b"2100-02-29T00:00:00Z", b"2000-02-29T23:59:59+00:00", b"2026-10-03T19:58:10-04:00",
                  b"2026-10-03T23:58:10Z", b"1791071890000", b"0001791071890000", b"2026-10-03T23:58:10z", b"2026-10-03t23:58:10Z", b"2026-10-03T24:00:00Z",
                  b"2026-10-03T23:58:60Z", b"2026-13-03T23:58:10Z", b"2026-10-03T23:58:10+24:00", b"2026-10-03T23:58:10+05:60", b"2026-10-03T23:58:10-00:00",
                  b"2026-10-03T23:58:10+0200x", b"00000000000000000000", b"99999999999999999999", b"0000-0000000000000000", b"1.79e12", b"-5", b"86400000"] {
            assert_eq!(parse_ts(s), parse_ts_ref(s), "{:?}", String::from_utf8_lossy(s));
        }
    }
    #[test]
    fn scanner_matches_split_line() {
        let mut r = Rng(42);
        let alphabet = b"ab,,,\"\"\n\n1 \r";
        for _ in 0..200_000 {
            let n = r.below(200) as usize;
            let data: Vec<u8> = (0..n).map(|_| alphabet[r.below(alphabet.len() as u64) as usize]).collect();
            for fields in [2usize, 4, 7] {
                let mut got: Vec<Vec<Vec<u8>>> = Vec::new();
                let mut want: Vec<Vec<Vec<u8>>> = Vec::new();
                macro_rules! run { ($n:literal) => {{
                    scan_lines::<$n>(&data, |f| got.push(f.iter().map(|x| x.to_vec()).collect()));
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
fn map_file(p: &Path) -> Option<&'static [u8]> {
    let f = File::open(p).ok()?;
    if f.metadata().ok()?.len() == 0 { return None; }
    let m = unsafe { Mmap::map(&f).ok()? };
    #[cfg(unix)]
    let _ = m.advise(memmap2::Advice::Sequential);
    let s: &'static [u8] = unsafe { std::slice::from_raw_parts(m.as_ptr(), m.len()) };
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
    parse_ts(rest[q1 + 1..q1 + 1 + q2].as_bytes()).expect("manifest timestamp")
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

fn build_links(dir: PathBuf) -> LinkTab {
    let files = map_dir(&dir);
    let parts: Vec<&'static [u8]> = files.iter().flat_map(|d| chunks(d, 4 << 20)).collect();
    let pairs: Vec<Vec<[u64; 4]>> = parts.par_iter().map(|part| {
        let mut v = Vec::with_capacity(part.len() / 16 + 4);
        scan_lines::<2>(part, |[a, b]| {
            if a.is_empty() || b.is_empty() { return; }
            v.push([xxh3_64(a), pack(a), xxh3_64(b), pack(b)]);
        });
        v
    }).collect();
    let npairs: usize = pairs.iter().map(|v| v.len()).sum();
    let mut idx: IdMap<u32> = IdMap::default();
    idx.reserve(npairs * 2);
    let mut names: Vec<u64> = Vec::with_capacity(npairs * 2);
    let mut keys: Vec<u64> = Vec::with_capacity(npairs * 2);
    let mut parent: Vec<u32> = Vec::with_capacity(npairs * 2);
    fn find(parent: &mut [u32], mut x: u32) -> u32 {
        let mut r = x;
        while parent[r as usize] != r { r = parent[r as usize]; }
        while parent[x as usize] != r { let n = parent[x as usize]; parent[x as usize] = r; x = n; }
        r
    }
    for v in &pairs {
        for &[ha, na, hb, nb] in v {
            let mut get = |h: u64, name: u64| -> u32 {
                let next = names.len() as u32;
                *idx.entry(h).or_insert_with(|| { names.push(name); keys.push(h); parent.push(next); next })
            };
            let (ia, ib) = (get(ha, na), get(hb, nb));
            let (ra, rb) = (find(&mut parent, ia), find(&mut parent, ib));
            if ra != rb {
                // the root is always the byte-wise smallest name of its set
                if unpack(names[ra as usize]) < unpack(names[rb as usize]) { parent[rb as usize] = ra; } else { parent[ra as usize] = rb; }
            }
        }
    }
    drop(idx);
    let cap = (names.len() * 2).next_power_of_two().max(16);
    let mask = cap - 1;
    let mut slots = vec![[0u64; 4]; cap];
    advise_huge(&slots);
    for i in 0..names.len() as u32 {
        let r = find(&mut parent, i) as usize;
        let h = keys[i as usize];
        let mut s = h as usize & mask;
        while slots[s][2] != 0 { s = (s + 1) & mask; }
        slots[s] = [h, keys[r], names[r], 0];
    }
    LinkTab { mask, slots }
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

/// Writes one Parquet file with at most one row group; `pages[c]` are column c's pages in row order.
fn write_parquet(path: &Path, cols: &[Col], nrows: usize, pages: &[Vec<Page>]) {
    let total: usize = pages.iter().flatten().map(|p| p.body[0].len() + p.body[1].len() + 24).sum();
    let mut f: Vec<u8> = Vec::with_capacity(total + 4096);
    f.extend_from_slice(b"PAR1");
    let mut chunks_meta: Vec<(usize, usize)> = Vec::new(); // (first page offset, bytes)
    for col in pages {
        let start = f.len();
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
            f.extend_from_slice(&h.b);
            f.extend_from_slice(p.body[0]);
            f.extend_from_slice(p.body[1]);
        }
        chunks_meta.push((start, f.len() - start));
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
    f.extend_from_slice(&t.b);
    f.extend_from_slice(&(t.b.len() as u32).to_le_bytes());
    f.extend_from_slice(b"PAR1");
    File::create(path).unwrap().write_all(&f).unwrap();
}

#[inline(always)]
fn put_str(v: &mut Vec<u8>, s: &[u8]) {
    v.extend_from_slice(&(s.len() as u32).to_le_bytes());
    v.extend_from_slice(s);
}

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
    let nb = (est_events / 16_000).next_power_of_two().clamp(64, 4096); // dedup buckets, sized to stay in cache
    let nb_shift = 64 - nb.trailing_zeros();
    let np = (est_events / 20_000).next_power_of_two().clamp(16, 4096); // person partitions
    let np_mask = (np - 1) as u64;
    let pbucket = move |pk: u64| -> usize { ((pk >> 40) & np_mask) as usize };
    let chunk = (ev_bytes / (threads * 8)).clamp(1 << 20, 16 << 20);
    let ev_parts: Vec<&'static [u8]> = ev_files.iter().flat_map(|d| chunks(d, chunk)).collect();
    let mut parsed: Vec<Vec<Vec<Ev>>> = ev_parts.par_iter().map(|part| {
        let est = part.len() / 64 / nb + 8;
        let mut acc: Vec<Vec<Ev>> = (0..nb).map(|_| Vec::with_capacity(est)).collect();
        scan_lines::<7>(part, |[id, user, ts, ingest, ty, product, price]| {
            if id.is_empty() { return; }
            let h = xxh3_128(id);
            let hi = (h >> 64) as u64;
            let ingest_ms = parse_ts(ingest);
            let mut e = Ev { eid: h as u64, user: 0, name: 0, ts: DEAD, eid2: hi as u32, ingest: i32::MIN, price: 0, cat: 0 };
            if let Some(ing) = ingest_ms {
                e.ingest = ((ing - ws).div_euclid(1000)).clamp(i32::MIN as i64 + 1, i32::MAX as i64) as i32;
            }
            (|| {
                if user.is_empty() || product.is_empty() { return; }
                let Some(t) = parse_ts(ts) else { return };
                if t < ws || t >= we { return; }
                let Some(ing) = ingest_ms else { return };
                if ing - t > DAY_MS { return; }
                match ty {
                    b"view" | b"cart" => {}
                    b"purchase" => {
                        let Some(p) = parse_price(price) else { return };
                        e.price = p;
                        e.cat = products.get(&xxh3_64(product)).copied().unwrap_or(0);
                    }
                    _ => return,
                }
                e.user = xxh3_64(user);
                e.name = pack(user);
                e.ts = t;
            })();
            unsafe { acc.get_unchecked_mut((hi >> nb_shift) as usize) }.push(e);
        });
        acc
    }).collect();
    lap(&format!("events parsed ({} dedup buckets, {} person partitions)", nb, np));

    let links = links_thread.join().unwrap();
    lap(&format!("links ready: {} slots", links.slots.len()));

    // ---- dedup each bucket, resolve people, count survivors per person partition
    let groups = (threads * 8).min(nb);
    let per_group = nb / groups; // both are powers of two or nb is a multiple: nb >= 64 and threads*8 may not divide
    let groups = nb.div_ceil(per_group);
    let parsed_ptr = Raw(parsed.as_mut_ptr());
    let nchunks = parsed.len();
    let counts: Vec<Vec<u32>> = (0..groups).into_par_iter().map(|g| {
        let mut cnt = vec![0u32; np];
        let mut table: Vec<u64> = Vec::new();
        let mut refs: Vec<*mut Ev> = Vec::new();
        for b in (g * per_group)..((g + 1) * per_group).min(nb) {
            // this group is the only one touching bucket b of every chunk
            let lists: Vec<&mut Vec<Ev>> = (0..nchunks).map(|c| unsafe { &mut *(*parsed_ptr.get().add(c)).as_mut_ptr().add(b) }).collect();
            let n: usize = lists.iter().map(|l| l.len()).sum();
            if n == 0 { continue; }
            let cap = (n * 2).next_power_of_two();
            let mask = cap - 1;
            table.clear();
            table.resize(cap, 0);
            refs.clear();
            for l in lists {
                for e in l.iter_mut() {
                    let i = refs.len() as u64 + 1;
                    let tag = e.eid >> 32;
                    let mut s = e.eid as usize & mask;
                    loop {
                        let t = table[s];
                        if t == 0 { table[s] = (tag << 32) | i; break; }
                        if t >> 32 == tag {
                            let o = unsafe { &mut *refs[(t as u32 - 1) as usize] };
                            if o.eid == e.eid && o.eid2 == e.eid2 {
                                if e.ingest < o.ingest { o.ts = DEAD; table[s] = (tag << 32) | i; } else { e.ts = DEAD; }
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
                for &r in blk { let e = unsafe { &*r }; if e.ts != DEAD { prefetch(links.slot(e.user)); } }
                for &r in blk {
                    let e = unsafe { &mut *r };
                    if e.ts == DEAD { continue; }
                    let (pk, name) = links.person(e.user, e.name);
                    e.user = pk;
                    e.name = name;
                    cnt[pbucket(pk)] += 1;
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
    unsafe { evs.set_len(total_ev); }
    let evs_ptr = Raw(evs.as_mut_ptr());
    ev_offs.into_par_iter().enumerate().for_each(|(g, mut off)| {
        for b in (g * per_group)..((g + 1) * per_group).min(nb) {
            for c in 0..nchunks {
                let l: &Vec<Ev> = unsafe { &*(*parsed_ptr.get().add(c)).as_ptr().add(b) };
                for e in l {
                    if e.ts == DEAD { continue; }
                    let p = pbucket(e.user);
                    unsafe { evs_ptr.get().add(off[p]).write(Sv { pk: e.user, ts: e.ts, name: e.name, price: e.price, cat: e.cat }); }
                    off[p] += 1;
                }
            }
        }
    });
    std::mem::forget(parsed); // freeing a million small buffers is slower than leaving them
    lap(&format!("events deduped: {} survive", total_ev));

    // ---- clicks: parse, validate, resolve people; copies are identical, so dedup happens after the sort
    let ck_files = map_dir(&data.join("clicks"));
    let ck_bytes: usize = ck_files.iter().map(|d| d.len()).sum();
    let ck_chunk = (ck_bytes / (threads * 8)).clamp(1 << 20, 16 << 20);
    let ck_parts: Vec<&'static [u8]> = ck_files.iter().flat_map(|d| chunks(d, ck_chunk)).collect();
    let ck_parsed: Vec<(Vec<Ck>, Vec<u32>)> = ck_parts.par_iter().map(|part| {
        let mut v: Vec<Ck> = Vec::with_capacity(part.len() / 40 + 4);
        scan_lines::<4>(part, |[id, user, camp, ts]| {
            if id.is_empty() || user.is_empty() { return; }
            let Some(t) = parse_ts(ts) else { return };
            if t < ws - WEEK_MS || t >= we { return; }
            let Some(&c) = campaigns.get(&xxh3_64(camp)) else { return };
            if camp_names[c as usize] != camp { return; }
            v.push(Ck { pk: xxh3_64(user), ts: t, id: pack(id), camp: c, pad: 0 });
        });
        let mut cnt = vec![0u32; np];
        for blk in v.chunks_mut(32) {
            for c in blk.iter() { prefetch(links.slot(c.pk)); }
            for c in blk.iter_mut() {
                c.pk = links.person(c.pk, 1).0;
                cnt[pbucket(c.pk)] += 1;
            }
        }
        (v, cnt)
    }).collect();
    let ck_counts: Vec<Vec<u32>> = ck_parsed.iter().map(|x| x.1.clone()).collect();
    let (ck_base, ck_offs) = scatter_offsets(&ck_counts);
    let total_ck = ck_base[np];
    let mut cks: Vec<Ck> = Vec::with_capacity(total_ck);
    advise_huge(&cks);
    unsafe { cks.set_len(total_ck); }
    let cks_ptr = Raw(cks.as_mut_ptr());
    ck_parsed.par_iter().zip(ck_offs.into_par_iter()).for_each(|((v, _), mut off)| {
        for c in v {
            let p = pbucket(c.pk);
            unsafe { cks_ptr.get().add(off[p]).write(*c); }
            off[p] += 1;
        }
    });
    lap(&format!("clicks parsed: {} valid", total_ck));

    // ---- per partition: sort, sessionize, credit, assists, user_daily pages
    let camp_acc: PerThread<Vec<[i64; 4]>> = PerThread((0..threads).map(|_| UnsafeCell::new(vec![[0i64; 4]; ncamp * ndays])).collect());
    let parts: Vec<PartOut> = (0..np).into_par_iter().map(|b| {
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
        for person in 0..people {
            let (i, j) = (e_off[person] as usize, e_off[person + 1] as usize);
            ev[i..j].sort_unstable_by_key(|e| e.ts);
            // this person's clicks: latest ts last; among equal ts the smallest click_id last; copies dropped
            let pc_all = &mut cks_sorted[c_off[person] as usize..c_off[person + 1] as usize];
            pc_all.sort_unstable_by(|x, y| x.ts.cmp(&y.ts).then_with(|| if x.id == y.id { std::cmp::Ordering::Equal } else { unpack(y.id).cmp(unpack(x.id)) }));
            let mut w = 0usize;
            for r in 0..pc_all.len() {
                if w > 0 && pc_all[w - 1].ts == pc_all[r].ts && unpack(pc_all[w - 1].id) == unpack(pc_all[r].id) { continue; }
                pc_all[w] = pc_all[r];
                w += 1;
            }
            let pc: &[Ck] = &pc_all[..w];
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
                let start = ev[k].ts;
                let day = (start.div_euclid(DAY_MS) - day0) as usize;
                if day != cur_day {
                    if cur_day != usize::MAX { flush(&mut p, cur_day, d_sessions, d_events, d_rev, &mut cat_sum, &mut touched); }
                    cur_day = day; d_sessions = 0; d_events = 0; d_rev = 0;
                    runs.push((day, starts.len()));
                }
                let (mut n, mut rev, mut prev) = (0i64, 0i64, start);
                while k < j && ev[k].ts - prev <= GAP_MS {
                    let e = &ev[k];
                    if e.price > 0 {
                        rev += e.price as i64;
                        if cat_sum[e.cat as usize] == 0 { touched.push(e.cat); }
                        cat_sum[e.cat as usize] += e.price as i64;
                    }
                    n += 1; prev = e.ts; k += 1;
                }
                d_sessions += 1; d_events += n; d_rev += rev;
                starts.push(start);
                while cptr < pc.len() && pc[cptr].ts <= start { cptr += 1; }
                let c = if cptr > 0 && start - pc[cptr - 1].ts <= WEEK_MS { pc[cptr - 1].camp as usize } else { 0 };
                let cell = &mut camp[c * ndays + day];
                cell[0] += 1; cell[1] += (rev > 0) as i64; cell[2] += rev;
            }
            flush(&mut p, cur_day, d_sessions, d_events, d_rev, &mut cat_sum, &mut touched);

            // assists: per campaign, merge the [click, click + 7 days] spans and count the sessions inside, by day
            if !pc.is_empty() {
                ct.clear();
                ct.extend(pc.iter().map(|c| (c.camp, c.ts)));
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
    // Skip destructors: the OS frees everything at exit.
    std::process::exit(0);
}
