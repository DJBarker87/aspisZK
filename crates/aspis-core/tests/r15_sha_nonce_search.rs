//! Bounded offline research search, never called by the prover/verifier.
//! A chosen nonce is not the ordinary honest nonce distribution.
use sha2::{Digest, Sha256};

fn queries(prefix: [u8; 32], nonce: u64) -> Option<Vec<u32>> {
    let mut input = [0u8; 42];
    input[..32].copy_from_slice(&prefix);
    input[33] = 5; // DOM_ABSORB=0, GRIND_NONCE=5.
    input[34..].copy_from_slice(&nonce.to_le_bytes());
    let mut state: [u8; 32] = Sha256::digest(input).into();
    let mut accepted = Vec::with_capacity(22);
    for _ in 0..8 {
        let mut key = [0u8; 33];
        key[..32].copy_from_slice(&state);
        key[32] = 1;
        let output = Sha256::digest(key);
        for word in output.chunks_exact(4) {
            let q = u32::from_le_bytes(word.try_into().unwrap()) & ((1 << 18) - 1);
            if !accepted.contains(&q) {
                accepted.push(q);
                if accepted.len() == 22 {
                    // Only the returned IDs matter here. Full host replay
                    // must check the source's final state consumption too.
                    return Some(accepted);
                }
            }
        }
        key[32] = 2;
        state = Sha256::digest(key).into();
    }
    None
}

#[test]
#[ignore = "explicit bounded SHA-only nonce-search experiment"]
fn r15_bounded_sha_nonce_search() {
    let hex = std::env::var("ASPIS_R15_PRE_NONCE").expect("32-byte prefix hex");
    assert_eq!(hex.len(), 64);
    let prefix = std::array::from_fn(|i| u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).unwrap());
    let start: u64 = std::env::var("ASPIS_R15_SEARCH_START")
        .unwrap_or_else(|_| "0".into())
        .parse()
        .unwrap();
    let count: u64 = std::env::var("ASPIS_R15_SEARCH_COUNT")
        .expect("explicit attempt cap")
        .parse()
        .unwrap();
    assert!(
        count > 0 && count <= 1_000_000,
        "one bounded preflight chunk at a time"
    );
    let end = start.checked_add(count).unwrap();
    for nonce in start..end {
        if let Some(q) = queries(prefix, nonce) {
            if q.contains(&4) && q.contains(&6) {
                println!(
                    "R15_SHA_FOUND nonce={nonce} queries={q:?} checked={}",
                    nonce - start + 1
                );
                return;
            }
        }
    }
    println!("R15_SHA_NO_HIT start={start} count={count}; not evidence of privacy");
}
