#[cfg(test)]
mod research_merkle_input_tests {
    extern crate std;
    use super::*;
    use alloc::vec;
    use sha2::{Digest,Sha256};
    fn hash(parts:&[&[u8]])->[u8;32]{
        let mut h=Sha256::new();for p in parts{h.update(p);}h.finalize().into()
    }
    // Capture literal bytes rather than relying only on equality of digests.
    std::thread_local!{static EXPECTED:std::cell::RefCell<Vec<u8>>=const{std::cell::RefCell::new(Vec::new())};}
    fn checked_hash(parts:&[&[u8]])->[u8;32]{
        let flat:Vec<u8>=parts.iter().flat_map(|p|p.iter().copied()).collect();
        EXPECTED.with(|e|assert_eq!(*e.borrow(),flat));
        #[cfg(v8_merkle_slices)] assert_eq!(parts.iter().map(|p|p.len()).collect::<Vec<_>>(),[1,26,26]);
        #[cfg(not(v8_merkle_slices))] assert_eq!(parts.iter().map(|p|p.len()).collect::<Vec<_>>(),[53]);
        hash(parts)
    }
    #[test]
    fn arbitrary_parent_bytes_and_sha_are_identical(){
        let mut rng=0x6d65_726b_6c65_7638u64;
        let mut cases=0;
        let mut run=|l:[u8;26],r:[u8;26]|{
            let mut literal=Vec::from([0x11]);literal.extend(l);literal.extend(r);
            EXPECTED.with(|e|*e.borrow_mut()=literal.clone());
            assert_eq!(node_hash_v7(checked_hash,&l,&r),truncate_sha256_v7(hash(&[&literal])));
            cases+=1;
        };
        for position in 0..52{for value in 0..=255u8{
            let mut pair=[0u8;52];pair[position]=value;
            run(pair[..26].try_into().unwrap(),pair[26..].try_into().unwrap());
        }}
        for _ in 0..1024{
            let pair:[u8;52]=core::array::from_fn(|_|{rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;rng as u8});
            run(pair[..26].try_into().unwrap(),pair[26..].try_into().unwrap());
        }
        assert_eq!(cases,14336);
    }
    #[test]
    fn hashfn_type_alone_does_not_guarantee_segment_independence(){
        fn bad_backend(parts:&[&[u8]])->[u8;32]{[parts.len() as u8;32]}
        assert_ne!(bad_backend(&[&[0u8;53]]),bad_backend(&[&[0x11],&[0u8;26],&[0u8;26]]));
    }
    #[test]
    fn all_small_frontiers_and_malformed_controls(){
        // Exhaustive nonempty depth-three schedules, with independent full
        // trees and explicit frontier construction. No query nonce search.
        for mask in 1u32..256{
            let leaves:Vec<_>=(0..8).map(|i|(i,[i as u8;26],[(i+80) as u8;26])).collect();
            let mut layers=vec![leaves.clone()];
            for _ in 0..3{
                let next=layers.last().unwrap().chunks_exact(2).map(|v|{
                    let parent=|a:[u8;26],b:[u8;26]|{
                        let mut bytes=Vec::from([0x11]);bytes.extend(a);bytes.extend(b);
                        truncate_sha256_v7(hash(&[&bytes]))};
                    (v[0].0>>1,parent(v[0].1,v[1].1),parent(v[0].2,v[1].2))
                }).collect();layers.push(next);
            }
            let entries:Vec<_>=leaves.into_iter().filter(|v|mask&(1<<v.0)!=0).collect();
            let mut ids:Vec<u32>=entries.iter().map(|e|e.0).collect();
            let(mut a,mut b)=(vec![],vec![]);
            for layer in &layers[..3]{
                for &i in &ids{if ids.binary_search(&(i^1)).is_err(){
                    a.extend(layer[(i^1) as usize].1);b.extend(layer[(i^1) as usize].2);
                }}
                for i in &mut ids{*i>>=1;}ids.dedup();
            }
            let roots=(&layers[3][0].1,&layers[3][0].2);
            let verify=|e:&[(u32,V7Digest,V7Digest)],a:&[u8],b:&[u8]|{
                verify_two_minimal_subtrees_v7_bytes(hash,roots,3,e,(a,b),&mut vec![],&mut vec![])};
            assert!(verify(&entries,&a,&b));
            if !a.is_empty(){let mut bad=a.clone();bad[0]^=1;assert!(!verify(&entries,&bad,&b));
                assert!(!verify(&entries,&a[..a.len()-1],&b));}
            let mut extra=a.clone();extra.extend([0;26]);assert!(!verify(&entries,&extra,&b));
            let mut bad=entries.clone();bad[0].1[0]^=1;assert!(!verify(&bad,&a,&b));
            bad=entries.clone();bad.insert(0,bad[0]);assert!(!verify(&bad,&a,&b));
            assert!(!verify(&[],&a,&b));
        }
    }
}
