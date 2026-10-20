use aspis_core::{field::{M31, QM31}, state_only_prefix::r0::statement_points};
use aspis_r1_cost_probe::multiproof::{node_count, Arity};
fn hash(parts:&[&[u8]]) -> [u8;32] {
    use sha2::{Digest,Sha256}; let mut h=Sha256::new(); for p in parts {h.update(p);} h.finalize().into()
}
fn main() {
    let mut state = 0x20261020u64;
    let mut next = || { state ^= state << 13; state ^= state >> 7; state ^= state << 17; (state % 2147483647) as u32 };
    for trial in 0..4096 {
        let z = core::array::from_fn(|i| {
            let words = if trial < 3 { [if trial == 0 {0} else if trial == 1 {1} else {2147483646}; 4] } else {core::array::from_fn(|_| next())};
            let mut b = [0u8;16]; for j in 0..4 {b[4*j..4*j+4].copy_from_slice(&words[j].to_le_bytes());}
            let _ = i; QM31::from_le_bytes(&b).unwrap()
        });
        let p = statement_points(&z);
        for c in 0..10 { assert_eq!(p[0][c],z[c]); assert_eq!(p[2][c], if c==6 || c==7 {QM31::ONE.sub(z[c])} else {z[c]}); }
        for c in [5,4,9,8] {assert_eq!(p[0][c],p[2][c]);}
    }
    let spread = |n:u32,bits:u32| {let mut v:Vec<_>=(0..n).map(|i|i.reverse_bits()>>(32-bits)).collect();v.sort();v};
    let mut counts=Vec::new();
    for n in [10,12] {for bits in [18,16] {let v=spread(n,bits); counts.push(node_count(Arity::Two,&v).unwrap());}}
    assert_eq!(counts,vec![146,128,172,150]);
    assert_eq!(2*(counts[0]+counts[2])+counts[1]+counts[3],914);
    let global:Vec<_>=(0..22u32).map(|j|j.reverse_bits()>>(32-18)).collect();
    let mut full_counts=Vec::new();
    for range in [0..10,10..22] {for tree in 0..3 {
        let mut ix:Vec<_>=global[range.clone()].iter().map(|&u|if tree==2 {u/4} else {u}).collect();ix.sort();ix.dedup();
        full_counts.push(node_count(Arity::Two,&ix).unwrap());
    }}
    assert_eq!(full_counts,vec![146,146,128,172,172,150]);
    assert_eq!(global.iter().copied().collect::<std::collections::BTreeSet<_>>().len(),22);
    use aspis_r1_cost_probe::multiproof::{BinaryTree,verify};
    use aspis_core::digest::LegacyHashFn;
    let leaves:Vec<_>=(0..1u32<<18).map(|i|hash(&[b"cu-bound3-leaf",&i.to_le_bytes()])).collect();
    let tree=BinaryTree::new(LegacyHashFn(hash),leaves).unwrap();
    for n in [10,12] {for bits in [18,16] {
        let offset = if n == 10 {0} else {10};
        let mut idx:Vec<_>=(offset..offset+n).map(|j:u32|j.reverse_bits()>>(32-bits)).collect();idx.sort();
        let lv:Vec<_>=idx.iter().map(|i|hash(&[b"cu-bound3-leaf",&i.to_le_bytes()])).collect();
        let nodes=tree.multiproof(&idx).unwrap();
        assert!(verify(LegacyHashFn(hash),Arity::Two,&tree.root(),&idx,&lv,&nodes));
        let mut bad=nodes.clone();bad[0]^=1;
        assert!(!verify(LegacyHashFn(hash),Arity::Two,&tree.root(),&idx,&lv,&bad));
    }}
    let _=M31::ONE;
    println!("{{\"X-WEIGHTS-S2\":\"PASS\",\"statement_point_trials\":4096,\"factor_coordinates\":[5,4,9,8],\"bit_reversed_counts\":[146,128,172,150],\"six_slot_total\":914,\"global_22_distinct_bit_reversed_counts\":[146,146,128,172,172,150],\"bit_reversed_verified_components\":4,\"mutations_rejected\":4,\"whole_transaction_bit_reversed\":false}}");
}
