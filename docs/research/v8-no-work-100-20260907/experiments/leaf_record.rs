//! Research-only descriptor fusion, after the fixed-record parser.
use super::*;

#[inline]
pub(super) fn c2(hashfn:corelib::HashFn,record:&[u8])->[u8;26]{
    // The caller's slice has length REC=621 by construction. C2 is followed
    // immediately by salt32. C1 is NOT contiguous with its shared salt.
    truncate_sha256_v7(corelib::state_only_private_merkle::private_leaf_hash_record(
        hashfn,V7_C2_TREE_TAG,&record[403..621]))
}

#[cfg(test)]
mod tests {
    use super::*;
    std::thread_local!{static EXPECTED:std::cell::RefCell<Vec<u8>>=const{std::cell::RefCell::new(Vec::new())};}
    fn capture(parts:&[&[u8]])->[u8;32]{
        assert_eq!(parts.iter().map(|s|s.len()).collect::<Vec<_>>(),[2,218]);
        let flat:Vec<u8>=parts.iter().flat_map(|s|s.iter().copied()).collect();
        EXPECTED.with(|e|assert_eq!(*e.borrow(),flat));
        hash(parts)
    }
    fn check(r:&[u8;REC]){
        let salt:&[u8;32]=r[589..621].try_into().unwrap();
        let mut expected=Vec::from([0x10,V7_C2_TREE_TAG]);
        expected.extend_from_slice(&r[403..589]);expected.extend_from_slice(salt);
        EXPECTED.with(|e|*e.borrow_mut()=expected);
        assert_eq!(c2(capture,r),private_leaf_hash_v7(hash,V7_C2_TREE_TAG,&r[403..589],salt));
    }
    #[test]
    fn literal_record_bytes_and_hashes(){
        // All positions, including C1 bytes deliberately excluded from C2.
        for position in 0..REC{for value in 0..=255u8{
            let mut r=[0;REC];r[position]=value;check(&r);
        }}
        let mut rng=0x6c65_6166_7638_2026u64;
        for _ in 0..1024{
            let r=core::array::from_fn(|_|{rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;rng as u8});check(&r);
        }
    }
    #[test]
    fn actual_parser_keeps_all_records_and_rejects_bad_boundaries(){
        let minimum=HEAD+Q*REC;
        for n in [0,HEAD-1,HEAD,minimum-1,minimum+1,40281,40283]{
            assert!(matches!(parse(&vec![0;n]),Err(Error::Length)));
        }
        for frontier_nodes in 0..=296{
            let b=vec![0;minimum+52*frontier_nodes];
            let w=parse(&b).unwrap();assert_eq!(w.records.len(),Q*REC);
            for i in 0..Q{let r=&w.records[i*REC..(i+1)*REC];
                assert_eq!(r.len(),REC);assert_eq!(r[403..621].len(),218);
                assert_eq!(c2(hash,r),private_leaf_hash_v7(hash,V7_C2_TREE_TAG,&r[403..589],r[589..621].try_into().unwrap()));
            }
        }
        let mut b=vec![0;minimum];b[..4].copy_from_slice(&0x7fff_ffffu32.to_le_bytes());
        assert!(matches!(parse(&b),Err(Error::Canonical)));
        // Parsing does not establish packed-leaf canonicality. That existing
        // gamma check still runs BEFORE either leaf hashing path.
    }
}
