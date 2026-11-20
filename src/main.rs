// Shopping Sessions: Rust implementation of rules.md.
// Identity of event IDs, user IDs, products and campaigns is by 128-bit xxh3 of the exact bytes
// (collision odds around 1e-23 at 60M rows); click IDs are compared as bytes.
use std::fs::File;
use std::hash::{BuildHasherDefault, Hasher};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Instant;

use arrow_array::{ArrayRef, Date32Array, Int64Array, RecordBatch, StringArray};
use arrow_schema::{DataType, Field, Schema};
use hashbrown::HashMap;
use memmap2::Mmap;
use parquet::arrow::ArrowWriter;
use parquet::basic::Compression;
use parquet::file::properties::WriterProperties;
use rayon::prelude::*;
use xxhash_rust::xxh3::xxh3_128;

const DAY_MS: i64 = 86_400_000;
const GAP_MS: i64 = 1_800_000;
const WEEK_MS: i64 = 604_800_000;
const NB: usize = 256; // partitions
const CHUNK: usize = 8 << 20;

#[derive(Default)]
struct IdHasher(u64);
impl Hasher for IdHasher {
    fn finish(&self) -> u64 { self.0 }
    fn write(&mut self, _: &[u8]) { unreachable!() }
    fn write_u128(&mut self, v: u128) { self.0 = (v as u64) ^ ((v >> 64) as u64); }
}
type IdMap<V> = HashMap<u128, V, BuildHasherDefault<IdHasher>>;

#[derive(Clone, Copy)]
struct Name { ptr: *const u8, len: u32 }
unsafe impl Send for Name {}
unsafe impl Sync for Name {}
impl Name {
    fn of(b: &[u8]) -> Name { Name { ptr: b.as_ptr(), len: b.len() as u32 } }
    fn bytes(&self) -> &'static [u8] { unsafe { std::slice::from_raw_parts(self.ptr, self.len as usize) } }
}

#[derive(Clone, Copy)]
struct Sv { pk: u128, ts: i64, name: Name, price: u32, cat: u32 }
#[derive(Clone, Copy)]
struct Ev { eid: u128, ingest: i64, valid: bool, sv: Sv }
#[derive(Clone, Copy)]
struct Ck { pk: u128, ts: i64, id: Name, camp: u32 }

// ---------------------------------------------------------------- line splitting
/// Splits one line into exactly N fields and strips whole-field quotes. None if malformed.
#[inline]
fn fields<'a, const N: usize>(line: &'a [u8]) -> Option<[&'a [u8]; N]> {
    let mut out: [&[u8]; N] = [&[]; N];
    let mut n = 0;
    let mut start = 0;
    let len = line.len();
    let mut i = 0;
    loop {
        if i == len || line[i] == b',' {
            if n == N { return None; }
            let f = &line[start..i];
            let f = if !f.is_empty() && f[0] == b'"' {
                if f.len() < 2 || f[f.len() - 1] != b'"' { return None; }
                let inner = &f[1..f.len() - 1];
                if memchr::memchr(b'"', inner).is_some() { return None; }
                inner
            } else {
                if memchr::memchr(b'"', f).is_some() { return None; }
                f
            };
            out[n] = f;
            n += 1;
            start = i + 1;
            if i == len { break; }
        }
        i += 1;
    }
    if n == N { Some(out) } else { None }
}

fn chunks(data: &[u8]) -> Vec<(usize, usize)> {
    // Skip the header line, then cut at line starts.
    let body = match memchr::memchr(b'\n', data) { Some(p) => p + 1, None => data.len() };
    let mut cuts = vec![body];
    let mut p = body + CHUNK;
    while p < data.len() {
        match memchr::memchr(b'\n', &data[p..]) {
            Some(q) => { cuts.push(p + q + 1); p = p + q + 1 + CHUNK; }
            None => break,
        }
    }
    cuts.push(data.len());
    cuts.windows(2).filter(|w| w[0] < w[1]).map(|w| (w[0], w[1])).collect()
}

#[inline]
fn for_lines<'a>(mut data: &'a [u8], mut f: impl FnMut(&'a [u8])) {
    while !data.is_empty() {
        match memchr::memchr(b'\n', data) {
            Some(p) => { f(&data[..p]); data = &data[p + 1..]; }
            None => { f(data); break; }
        }
    }
}

// ---------------------------------------------------------------- timestamps
#[inline]
fn d2(b: &[u8], i: usize) -> Option<i64> {
    let (a, c) = (b[i].wrapping_sub(b'0'), b[i + 1].wrapping_sub(b'0'));
    if a > 9 || c > 9 { None } else { Some((a * 10 + c) as i64) }
}
#[inline]
fn days_from_civil(y: i64, m: i64, d: i64) -> i64 {
    let y = if m <= 2 { y - 1 } else { y };
    let era = if y >= 0 { y } else { y - 399 } / 400;
    let yoe = y - era * 400;
    let doy = (153 * (if m > 2 { m - 3 } else { m + 9 }) + 2) / 5 + d - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * 146097 + doe - 719468
}
/// Epoch milliseconds, or None for a bad timestamp (window not checked here).
#[inline]
fn parse_ts(s: &[u8]) -> Option<i64> {
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
    // F3: ASCII digits only.
    let mut i = 0;
    while i < n && s[i] == b'0' { i += 1; }
    let mut v: i64 = 0;
    let digits = n - i;
    for &c in &s[..i] { if c != b'0' { return None; } }
    for &c in &s[i..] {
        let d = c.wrapping_sub(b'0');
        if d > 9 { return None; }
        if digits <= 18 { v = v * 10 + d as i64; }
    }
    if digits > 18 { None } else { Some(v) } // too long for any window: bad either way
}
#[inline]
fn parse_price(s: &[u8]) -> Option<u32> {
    if s.is_empty() { return None; }
    let mut i = 0;
    while i < s.len() && s[i] == b'0' { i += 1; }
    let rest = &s[i..];
    if rest.is_empty() || rest.len() > 8 { // all zeros, or over 99,999,999
        for &c in rest { if c.wrapping_sub(b'0') > 9 { return None; } }
        return None;
    }
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
fn manifest_ts(text: &str, key: &str) -> i64 {
    let p = text.find(key).expect("manifest key");
    let rest = &text[p + key.len()..];
    let a = rest.find(':').unwrap();
    let rest = &rest[a + 1..];
    let q1 = rest.find('"').unwrap();
    let q2 = rest[q1 + 1..].find('"').unwrap();
    parse_ts(rest[q1 + 1..q1 + 1 + q2].as_bytes()).expect("manifest timestamp")
}

struct Person { pk: u128, name: Name }

fn main() {
    let t0 = Instant::now();
    let data = PathBuf::from(std::env::var("DATA_DIR").unwrap_or_else(|_| "/data".into()));
    let out = PathBuf::from(std::env::var("OUTPUT_DIR").unwrap_or_else(|_| "/output".into()));
    let threads = std::env::var("NCPU").ok().and_then(|s| s.parse::<usize>().ok()).filter(|&n| n > 0)
        .unwrap_or_else(|| std::thread::available_parallelism().map(|n| n.get()).unwrap_or(8));
    rayon::ThreadPoolBuilder::new().num_threads(threads).build_global().unwrap();
    let lap = |what: &str| eprintln!("[{:7.3}s] {}", t0.elapsed().as_secs_f64(), what);

    let mf = std::fs::read_to_string(data.join("manifest.json")).expect("manifest.json");
    let ws = manifest_ts(&mf, "\"window_start\"");
    let we = manifest_ts(&mf, "\"window_end\"");
    let day0 = ws.div_euclid(DAY_MS);
    let ndays = ((we - 1).div_euclid(DAY_MS) - day0 + 1).max(1) as usize;

    // ---- products and campaigns
    let mut cats: Vec<&[u8]> = vec![b"unknown"];
    let mut cat_idx: HashMap<&[u8], u32> = HashMap::new();
    cat_idx.insert(b"unknown", 0);
    let mut products: IdMap<u32> = IdMap::default();
    if let Some(d) = map_file(&data.join("products.csv")) {
        for (a, b) in chunks(d) {
            for_lines(&d[a..b], |l| if let Some([p, c]) = fields::<2>(l) {
                let next = cats.len() as u32;
                let ci = *cat_idx.entry(c).or_insert_with(|| { cats.push(c); next });
                products.entry(xxh3_128(p)).or_insert(ci);
            });
        }
    }
    // rank of each category in byte order, for ties
    let mut order: Vec<u32> = (0..cats.len() as u32).collect();
    order.sort_by(|&a, &b| cats[a as usize].cmp(cats[b as usize]));
    let mut cat_rank = vec![0u32; cats.len()];
    for (r, &c) in order.iter().enumerate() { cat_rank[c as usize] = r as u32; }

    let mut camp_names: Vec<&[u8]> = vec![b"organic"];
    let mut camp_chan: Vec<&[u8]> = vec![b"organic"];
    let mut campaigns: IdMap<u32> = IdMap::default();
    if let Some(d) = map_file(&data.join("campaigns.csv")) {
        for (a, b) in chunks(d) {
            for_lines(&d[a..b], |l| if let Some([c, ch]) = fields::<2>(l) {
                if c.is_empty() { return; }
                let next = camp_names.len() as u32;
                campaigns.entry(xxh3_128(c)).or_insert_with(|| { camp_names.push(c); camp_chan.push(ch); next });
            });
        }
    }
    let ncamp = camp_names.len();

    // ---- links: union-find, each person named by the byte-wise smallest ID
    let link_files: Vec<&'static [u8]> = list_csv(&data.join("links")).iter().filter_map(|p| map_file(p)).collect();
    let pairs: Vec<(&[u8], &[u8])> = link_files.par_iter()
        .flat_map_iter(|d| chunks(d).into_iter().map(move |(a, b)| &d[a..b]))
        .fold(Vec::new, |mut v, part| {
            for_lines(part, |l| if let Some([a, b]) = fields::<2>(l) {
                if !a.is_empty() && !b.is_empty() { v.push((a, b)); }
            });
            v
        })
        .reduce(Vec::new, |mut a, mut b| { a.append(&mut b); a });
    let mut idx: IdMap<u32> = IdMap::default();
    idx.reserve(pairs.len());
    let mut names: Vec<&[u8]> = Vec::new();
    let mut keys: Vec<u128> = Vec::new();
    let mut parent: Vec<u32> = Vec::new();
    fn find(parent: &mut [u32], mut x: u32) -> u32 {
        let mut r = x;
        while parent[r as usize] != r { r = parent[r as usize]; }
        while parent[x as usize] != r { let n = parent[x as usize]; parent[x as usize] = r; x = n; }
        r
    }
    for &(a, b) in &pairs {
        let mut get = |s: &'static [u8]| -> u32 {
            let k = xxh3_128(s);
            let next = names.len() as u32;
            *idx.entry(k).or_insert_with(|| { names.push(s); keys.push(k); parent.push(next); next })
        };
        let (ia, ib) = (get(a), get(b));
        let (ra, rb) = (find(&mut parent, ia), find(&mut parent, ib));
        if ra != rb {
            // the root is always the smallest name of its set
            if names[ra as usize] < names[rb as usize] { parent[rb as usize] = ra; } else { parent[ra as usize] = rb; }
        }
    }
    let mut linked: IdMap<Person> = IdMap::default();
    linked.reserve(names.len());
    for i in 0..names.len() as u32 {
        let r = find(&mut parent, i) as usize;
        linked.insert(keys[i as usize], Person { pk: keys[r], name: Name::of(names[r]) });
    }
    drop(idx);
    lap(&format!("links: {} pairs, {} ids", pairs.len(), names.len()));

    let person = |user: &'static [u8]| -> (u128, Name) {
        let k = xxh3_128(user);
        match linked.get(&k) { Some(p) => (p.pk, p.name), None => (k, Name::of(user)) }
    };
    #[inline]
    fn bucket(k: u128) -> usize { ((k >> 96) as usize) & (NB - 1) }

    // ---- events: parse, then dedup on event_id
    let ev_parts: Vec<&'static [u8]> = list_csv(&data.join("events")).iter().filter_map(|p| map_file(p))
        .flat_map(|d| chunks(d).into_iter().map(move |(a, b)| &d[a..b])).collect();
    let parsed: Vec<Vec<Vec<Ev>>> = ev_parts.par_iter()
        .fold(|| (0..NB).map(|_| Vec::new()).collect::<Vec<Vec<Ev>>>(), |mut acc, part| {
            for_lines(part, |l| {
                let Some([id, user, ts, ingest, ty, product, price]) = fields::<7>(l) else { return };
                if id.is_empty() { return; }
                let eid = xxh3_128(id);
                let ingest_ms = parse_ts(ingest);
                let mut sv = Sv { pk: 0, ts: 0, name: Name::of(b""), price: 0, cat: 0 };
                let valid = (|| {
                    if user.is_empty() || product.is_empty() { return false; }
                    let Some(t) = parse_ts(ts) else { return false };
                    if t < ws || t >= we { return false; }
                    let Some(ing) = ingest_ms else { return false };
                    if ing - t > DAY_MS { return false; }
                    match ty {
                        b"view" | b"cart" => {}
                        b"purchase" => {
                            let Some(p) = parse_price(price) else { return false };
                            sv.price = p;
                            sv.cat = products.get(&xxh3_128(product)).copied().unwrap_or(0);
                        }
                        _ => return false,
                    }
                    let (pk, name) = person(user);
                    sv.pk = pk; sv.name = name; sv.ts = t;
                    true
                })();
                acc[bucket(eid)].push(Ev { eid, ingest: ingest_ms.unwrap_or(i64::MIN), valid, sv });
            });
            acc
        })
        .collect();
    lap("events parsed");

    let survivors: Vec<Vec<Vec<Sv>>> = (0..NB).into_par_iter().map(|b| {
        let total: usize = parsed.iter().map(|p| p[b].len()).sum();
        let mut best: IdMap<Ev> = IdMap::default();
        best.reserve(total);
        for p in &parsed {
            for e in &p[b] {
                match best.entry(e.eid) {
                    hashbrown::hash_map::Entry::Vacant(v) => { v.insert(*e); }
                    hashbrown::hash_map::Entry::Occupied(mut o) => if e.ingest < o.get().ingest { o.insert(*e); }
                }
            }
        }
        let mut outb: Vec<Vec<Sv>> = (0..NB).map(|_| Vec::new()).collect();
        for e in best.values() { if e.valid { outb[bucket(e.sv.pk)].push(e.sv); } }
        outb
    }).collect();
    drop(parsed);
    lap("events deduped");

    // ---- clicks: parse and validate; copies are identical, so dedup happens after the sort
    let ck_parts: Vec<&'static [u8]> = list_csv(&data.join("clicks")).iter().filter_map(|p| map_file(p))
        .flat_map(|d| chunks(d).into_iter().map(move |(a, b)| &d[a..b])).collect();
    let clicks: Vec<Vec<Vec<Ck>>> = ck_parts.par_iter()
        .fold(|| (0..NB).map(|_| Vec::new()).collect::<Vec<Vec<Ck>>>(), |mut acc, part| {
            for_lines(part, |l| {
                let Some([id, user, camp, ts]) = fields::<4>(l) else { return };
                if id.is_empty() || user.is_empty() { return; }
                let Some(t) = parse_ts(ts) else { return };
                if t < ws - WEEK_MS || t >= we { return; }
                let Some(&c) = campaigns.get(&xxh3_128(camp)) else { return };
                let (pk, _) = person(user);
                acc[bucket(pk)].push(Ck { pk, ts: t, id: Name::of(id), camp: c });
            });
            acc
        })
        .collect();
    lap("clicks parsed");

    // ---- per partition: sessionize, credit, assists, user_daily rows
    struct Part {
        names: Vec<Name>, day: Vec<i32>, sessions: Vec<i64>, events: Vec<i64>, revenue: Vec<i64>, top: Vec<u32>,
        camp: Vec<[i64; 4]>, // [campaign * ndays + day] -> sessions, purchasing, revenue, assisted
    }
    const NO_CAT: u32 = u32::MAX;
    let parts: Vec<Part> = (0..NB).into_par_iter().map(|b| {
        let mut ev: Vec<Sv> = Vec::with_capacity(survivors.iter().map(|s| s[b].len()).sum());
        for s in &survivors { ev.extend_from_slice(&s[b]); }
        ev.sort_unstable_by_key(|e| (e.pk, e.ts));
        let mut ck: Vec<Ck> = Vec::with_capacity(clicks.iter().map(|s| s[b].len()).sum());
        for s in &clicks { ck.extend_from_slice(&s[b]); }
        // latest ts last; among equal ts the smallest click_id last
        ck.sort_unstable_by(|x, y| (x.pk, x.ts).cmp(&(y.pk, y.ts)).then_with(|| y.id.bytes().cmp(x.id.bytes())));
        ck.dedup_by(|x, y| x.pk == y.pk && x.ts == y.ts && x.id.bytes() == y.id.bytes());

        let mut p = Part { names: vec![], day: vec![], sessions: vec![], events: vec![], revenue: vec![], top: vec![],
                           camp: vec![[0i64; 4]; ncamp * ndays] };
        let mut cat_sum = vec![0i64; cats.len()];
        let mut touched: Vec<u32> = Vec::new();
        let mut starts: Vec<i64> = Vec::new();       // this person's session starts
        let mut runs: Vec<(usize, usize)> = Vec::new(); // (day index, first session index) per day
        let mut ct: Vec<(u32, i64)> = Vec::new();
        let (mut i, mut ci) = (0usize, 0usize);
        while i < ev.len() {
            let pk = ev[i].pk;
            let mut j = i;
            while j < ev.len() && ev[j].pk == pk { j += 1; }
            while ci < ck.len() && ck[ci].pk < pk { ci += 1; }
            let mut cj = ci;
            while cj < ck.len() && ck[cj].pk == pk { cj += 1; }
            let pc = &ck[ci..cj];
            starts.clear(); runs.clear();

            let name = ev[i].name;
            let mut k = i;
            let mut cptr = 0usize; // clicks with ts <= current session start
            // per-day accumulators
            let (mut cur_day, mut d_sessions, mut d_events, mut d_rev) = (usize::MAX, 0i64, 0i64, 0i64);
            let flush = |p: &mut Part, day: usize, s: i64, e: i64, r: i64, cat_sum: &mut Vec<i64>, touched: &mut Vec<u32>| {
                let mut best = NO_CAT;
                for &c in touched.iter() {
                    if best == NO_CAT || cat_sum[c as usize] > cat_sum[best as usize]
                        || (cat_sum[c as usize] == cat_sum[best as usize] && cat_rank[c as usize] < cat_rank[best as usize]) {
                        best = c;
                    }
                }
                for &c in touched.iter() { cat_sum[c as usize] = 0; }
                touched.clear();
                p.names.push(name); p.day.push((day0 + day as i64) as i32);
                p.sessions.push(s); p.events.push(e); p.revenue.push(r); p.top.push(best);
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
                let camp = if cptr > 0 && start - pc[cptr - 1].ts <= WEEK_MS { pc[cptr - 1].camp as usize } else { 0 };
                let cell = &mut p.camp[camp * ndays + day];
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
                    let (camp, lo) = ct[a];
                    let mut hi = lo + WEEK_MS;
                    a += 1;
                    while a < ct.len() && ct[a].0 == camp && ct[a].1 <= hi { hi = ct[a].1 + WEEK_MS; a += 1; }
                    let i0 = starts.partition_point(|&s| s < lo);
                    let i1 = starts.partition_point(|&s| s <= hi);
                    if i0 >= i1 { continue; }
                    for (r, &(day, first)) in runs.iter().enumerate() {
                        let end = if r + 1 < runs.len() { runs[r + 1].1 } else { starts.len() };
                        let (x, y) = (first.max(i0), end.min(i1));
                        if x < y { p.camp[camp as usize * ndays + day][3] += (y - x) as i64; }
                    }
                }
            }
            i = j; ci = cj;
        }
        p
    }).collect();
    lap("sessions, credit and assists done");

    // ---- write
    let props = WriterProperties::builder().set_compression(Compression::UNCOMPRESSED)
        .set_dictionary_enabled(false).set_statistics_enabled(parquet::file::properties::EnabledStatistics::None).build();
    std::fs::create_dir_all(out.join("user_daily")).unwrap();
    std::fs::create_dir_all(out.join("campaign_daily")).unwrap();
    let uschema = Arc::new(Schema::new(vec![
        Field::new("user_id", DataType::Utf8, false), Field::new("day", DataType::Date32, false),
        Field::new("sessions", DataType::Int64, false), Field::new("events", DataType::Int64, false),
        Field::new("revenue_cents", DataType::Int64, false), Field::new("top_category", DataType::Utf8, true),
    ]));
    let groups = (threads * 2).max(1);
    let per = NB.div_ceil(groups);
    let utf8 = |b: &[u8]| -> String { String::from_utf8_lossy(b).into_owned() };
    (0..groups).into_par_iter().for_each(|g| {
        let ps = &parts[(g * per).min(NB)..((g + 1) * per).min(NB)];
        let rows: usize = ps.iter().map(|p| p.names.len()).sum();
        if rows == 0 && g > 0 { return; }
        let uv: Vec<&str> = ps.iter().flat_map(|p| p.names.iter().map(|n| unsafe { std::str::from_utf8_unchecked(n.bytes()) })).collect();
        let user = StringArray::from(uv);
        let day = Date32Array::from_iter_values(ps.iter().flat_map(|p| p.day.iter().copied()));
        let s = Int64Array::from_iter_values(ps.iter().flat_map(|p| p.sessions.iter().copied()));
        let e = Int64Array::from_iter_values(ps.iter().flat_map(|p| p.events.iter().copied()));
        let r = Int64Array::from_iter_values(ps.iter().flat_map(|p| p.revenue.iter().copied()));
        let tv: Vec<Option<&str>> = ps.iter().flat_map(|p| p.top.iter().map(|&c|
            if c == NO_CAT { None } else { Some(unsafe { std::str::from_utf8_unchecked(cats[c as usize]) }) })).collect();
        let top = StringArray::from(tv);
        let cols: Vec<ArrayRef> = vec![Arc::new(user), Arc::new(day), Arc::new(s), Arc::new(e), Arc::new(r), Arc::new(top)];
        let batch = RecordBatch::try_new(uschema.clone(), cols).unwrap();
        let f = File::create(out.join("user_daily").join(format!("part-{g:03}.parquet"))).unwrap();
        let mut w = ArrowWriter::try_new(f, uschema.clone(), Some(props.clone())).unwrap();
        w.write(&batch).unwrap();
        w.close().unwrap();
    });

    let mut camp = vec![[0i64; 4]; ncamp * ndays];
    for p in &parts { for (a, b) in camp.iter_mut().zip(&p.camp) { for q in 0..4 { a[q] += b[q]; } } }
    let (mut cid, mut chan, mut cday) = (Vec::new(), Vec::new(), Vec::new());
    let mut cols4: [Vec<i64>; 4] = Default::default();
    for c in 0..ncamp { for d in 0..ndays {
        let v = camp[c * ndays + d];
        if v[0] == 0 && v[3] == 0 { continue; }
        cid.push(utf8(camp_names[c])); chan.push(utf8(camp_chan[c])); cday.push((day0 + d as i64) as i32);
        for q in 0..4 { cols4[q].push(v[q]); }
    } }
    let cschema = Arc::new(Schema::new(vec![
        Field::new("campaign_id", DataType::Utf8, false), Field::new("channel", DataType::Utf8, false),
        Field::new("day", DataType::Date32, false), Field::new("sessions", DataType::Int64, false),
        Field::new("purchasing_sessions", DataType::Int64, false), Field::new("revenue_cents", DataType::Int64, false),
        Field::new("assisted_sessions", DataType::Int64, false),
    ]));
    let [c0, c1, c2, c3] = cols4;
    let cols: Vec<ArrayRef> = vec![Arc::new(StringArray::from(cid)), Arc::new(StringArray::from(chan)), Arc::new(Date32Array::from(cday)),
        Arc::new(Int64Array::from(c0)), Arc::new(Int64Array::from(c1)), Arc::new(Int64Array::from(c2)), Arc::new(Int64Array::from(c3))];
    let batch = RecordBatch::try_new(cschema.clone(), cols).unwrap();
    let f = File::create(out.join("campaign_daily").join("part-000.parquet")).unwrap();
    let mut w = ArrowWriter::try_new(f, cschema, Some(props)).unwrap();
    w.write(&batch).unwrap();
    w.close().unwrap();
    lap("written");
    // Skip destructors: the OS frees everything at exit.
    std::process::exit(0);
}
