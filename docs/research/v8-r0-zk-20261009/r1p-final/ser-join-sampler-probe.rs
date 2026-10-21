//! Source sampler counterexample. No concrete-hash reachability claim.
use aspis_core::r0_transcript::queries_from_pairs;

fn sample(queries: [u32; 22]) -> [u32; 22] {
    let mut blocks = [[0u8; 32]; 8];
    for (i, query) in queries.iter().enumerate() {
        blocks[i / 8][4 * (i % 8)..4 * (i % 8 + 1)]
            .copy_from_slice(&query.to_le_bytes());
    }
    let advances = core::array::from_fn(|i| [i as u8; 32]);
    let (out, state) = queries_from_pairs(&blocks, &advances).unwrap();
    assert_eq!(out, queries);
    assert_eq!(state, advances[2]);
    out
}

// Exactly the C1/C2 batch-A index projection at prover.rs:266-269.
fn first_batch(queries: [u32; 22]) -> Vec<u32> {
    let mut idx: Vec<u32> = queries[0..11].to_vec();
    idx.sort();
    idx.dedup();
    idx
}

fn main() {
    let a = core::array::from_fn(|i| i as u32);
    let mut b = a;
    b.swap(10, 11);
    let a = sample(a);
    let b = sample(b);
    let mut set_a = a;
    let mut set_b = b;
    set_a.sort();
    set_b.sort();
    assert_eq!(set_a, set_b);
    assert!(set_a.windows(2).all(|w| w[0] < w[1]));
    assert_ne!(first_batch(a), first_batch(b));
    println!("{{\"first\":{:?},\"crossed\":{:?},\"first_batch\":{:?},\"crossed_batch\":{:?},\"same_set\":true,\"source_sampler_accepts_both\":true}}",
        a, b, first_batch(a), first_batch(b));
}
