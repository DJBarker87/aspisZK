//! Empirical off-curve rate and canonical-bump attempt distribution for
//! Pool-shaped PDA seeds. Native `solana-pubkey 2.4.0` (the Pool's version)
//! with the same `curve25519-dalek` predicate the runtime syscall uses.
//! Deterministic: inputs are SHA-256 counters under a fixed domain, so a
//! rerun reproduces the numbers exactly.
//!
//! usage: pool-pda-offcurve <n_candidates> <n_seeds>
use sha2::{Digest, Sha256};
use solana_pubkey::{bytes_are_curve_point, Pubkey};

fn prng(domain: &[u8], i: u64) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"aspis-pool-pda-study-20261019/");
    h.update(domain);
    h.update(i.to_le_bytes());
    h.finalize().into()
}

/// The runtime's search: bump 255 downwards, at most 255 attempts.
fn attempts(seeds: &[&[u8]], program: &Pubkey) -> Option<(u32, u8)> {
    let mut bump = [u8::MAX];
    for k in 1..=255u32 {
        let mut s: Vec<&[u8]> = seeds.to_vec();
        s.push(&bump);
        if Pubkey::create_program_address(&s, program).is_ok() {
            return Some((k, bump[0]));
        }
        bump[0] = bump[0].saturating_sub(1);
    }
    None
}

fn main() {
    let args: Vec<u64> = std::env::args().skip(1).map(|a| a.parse().unwrap()).collect();
    let (n_candidates, n_seeds) = (args[0], args[1]);

    // (1) Per-candidate rate on raw 32-byte strings and on real PDA preimages.
    let mut on_curve_raw = 0u64;
    for i in 0..n_candidates {
        if bytes_are_curve_point(prng(b"raw", i)) {
            on_curve_raw += 1;
        }
    }

    // (2) Marker-shaped seeds: [tag, pool, nullifier] under a fixed program id.
    let program = Pubkey::new_from_array(prng(b"program", 0));
    let pool = Pubkey::new_from_array(prng(b"pool", 0));
    let tag: &[u8] = b"aspis-pool-nullifier-v1";
    let mut hist = vec![0u64; 257];
    let mut tried = 0u64;
    let mut off_on_first = 0u64;
    let mut max_k = 0u32;
    // Every tried candidate (accepted or not) is a sample of the per-attempt
    // predicate on genuine PDA hash outputs.
    let mut candidates_tried = 0u64;
    let mut candidates_off = 0u64;
    for i in 0..n_seeds {
        let nullifier = prng(b"nullifier", i);
        match attempts(&[tag, pool.as_ref(), &nullifier], &program) {
            Some((k, _bump)) => {
                hist[k as usize] += 1;
                max_k = max_k.max(k);
                candidates_tried += u64::from(k);
                candidates_off += 1;
                if k == 1 {
                    off_on_first += 1;
                }
            }
            None => hist[256] += 1,
        }
        tried += 1;
    }
    let hist_json: Vec<String> = hist
        .iter()
        .enumerate()
        .filter(|(_, c)| **c > 0)
        .map(|(k, c)| format!("\"{}\":{}", k, c))
        .collect();
    println!(
        "{{\"crate\":\"solana-pubkey 2.4.0 native (curve25519-dalek decompress)\",\
\"raw_candidates\":{},\"raw_on_curve\":{},\"raw_off_curve_rate\":{:.6},\
\"marker_seeds\":{},\"marker_candidates_tried\":{},\"marker_candidates_off_curve\":{},\
\"marker_per_candidate_off_curve_rate\":{:.6},\"first_attempt_success\":{},\
\"max_attempts\":{},\"attempt_histogram\":{{{}}}}}",
        n_candidates,
        on_curve_raw,
        1.0 - on_curve_raw as f64 / n_candidates as f64,
        tried,
        candidates_tried,
        candidates_off,
        candidates_off as f64 / candidates_tried as f64,
        off_on_first,
        max_k,
        hist_json.join(",")
    );
}
