//! macOS-only SHA-256 schedule-search microbenchmark. Public synthetic seeds.
//! Counter format is a RESEARCH sampler, not the selected V7 transcript.
use std::{ffi::c_void, time::Instant};
#[link(name = "System")]
extern "C" {
    fn CC_SHA256(data: *const c_void, len: u32, out: *mut u8) -> *mut u8;
}
fn sha(x: &[u8]) -> [u8; 32] {
    let mut o = [0; 32];
    unsafe {
        CC_SHA256(x.as_ptr().cast(), x.len() as u32, o.as_mut_ptr());
    }
    o
}
fn count(xs: &[u32], d: u32) -> usize {
    let mut a = xs.to_vec();
    a.sort_unstable();
    let mut n = 0;
    for _ in 0..d {
        for &x in &a {
            if a.binary_search(&(x ^ 1)).is_err() {
                n += 1;
            }
        }
        for x in &mut a {
            *x /= 2;
        }
        a.dedup();
    }
    n
}
fn sample(base: [u8; 32], counter: u8, d: u32, q: usize) -> Option<Vec<u32>> {
    let mut input = base.to_vec();
    input.extend([0, 57, counter]);
    let mut state = sha(&input);
    let mut xs = Vec::new();
    for _ in 0..8 {
        let mut buf = state.to_vec();
        buf.push(1);
        let out = sha(&buf);
        buf[32] = 2;
        state = sha(&buf);
        for chunk in out.chunks_exact(4) {
            let x = u32::from_le_bytes(chunk.try_into().unwrap()) & ((1 << d) - 1);
            if !xs.contains(&x) {
                xs.push(x);
            }
            if xs.len() == q {
                return Some(xs);
            }
        }
    }
    None
}
fn main() {
    assert_eq!(
        sha(b"abc"),
        [
            0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40, 0xde, 0x5d, 0xae,
            0x22, 0x23, 0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61,
            0xf2, 0x00, 0x15, 0xad
        ]
    );
    for (d, q, cap) in [(20, 18, 246), (21, 17, 259), (22, 16, 272)] {
        let mut times = Vec::new();
        let mut attempts = Vec::new();
        let mut failures = 0;
        for seed in 0..2000u64 {
            let base = sha(&seed.to_le_bytes());
            let start = Instant::now();
            let mut success = false;
            let mut used = 0;
            for counter in 0..64 {
                used += 1;
                match sample(base, counter, d, q) {
                    Some(xs) => {
                        if count(&xs, d) <= cap {
                            success = true;
                            break;
                        }
                    }
                    None => break,
                }
            }
            if !success {
                failures += 1;
            }
            times.push(start.elapsed().as_nanos() as f64);
            attempts.push(used);
        }
        times.sort_by(f64::total_cmp);
        attempts.sort();
        println!("log={d},q={q},cap={cap},trials=2000,mean_ns={:.1},p95_ns={:.1},p99_ns={:.1},mean_attempts={:.3},p95_attempts={},failures={failures}",times.iter().sum::<f64>()/2000.,times[1899],times[1979],attempts.iter().sum::<usize>() as f64/2000.,attempts[1899]);
    }
}
