#[cfg(test)]
mod SDY_fidelity {
    use super::*;
    #[derive(Clone,Copy)]struct SDY_Hash;
    impl Digest32 for SDY_Hash {fn digest(&self,parts:&[&[u8]])->[u8;32] {[parts[1][0];32]}}
    #[test]
    fn SDY_multiproof() {
        for (index,leaf,sibling,digest) in [(8u32,5u8,2u8,5u8),(9,7,3,3),(10,9,4,4)] {
            let mut idx=[0u32;16];idx[0]=index;
            let mut val=[[0u8;32];16];val[0]=[leaf;32];
            let nodes=[sibling;224];
            let r=verify_in_place(SDY_Hash,Arity::Eight,&[0u8;32],&mut idx,&mut val,1,&nodes);
            std::println!("SDY multiproof {} {} {} => {} {:?} val0={} tailZero={}",index,leaf,sibling,r,idx,val[0][0],val[1..].iter().all(|v|*v==[0u8;32]));
            assert!(!r);assert_eq!(idx[0],1);assert_eq!(val[0],[digest;32]);assert_eq!(idx[1..],[0u32;15]);assert_eq!(val[1..],[[0u8;32];15]);
        }
    }
}
