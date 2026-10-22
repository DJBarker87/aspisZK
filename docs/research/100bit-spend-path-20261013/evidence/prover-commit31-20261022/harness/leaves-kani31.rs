#[cfg(kani)]
mod leaves_kani31 {
    use super::*;
    fn bytes()->Vec<u8> {let a:[u8;2]=kani::any();a.to_vec()}
    fn leaves()->BTreeMap<usize,(Vec<u8>,[u8;32])> {
        let mut t=BTreeMap::new();
        if kani::any() {let key:usize=kani::any();t.insert(key,(bytes(),kani::any()));}t
    }
    #[kani::proof]
    #[kani::unwind(12)]
    fn pair_transition() {
        let left=leaves();let right=leaves();let u:usize=kani::any();
        let c1=bytes();let c2=bytes();let s1:[u8;32]=kani::any();let s2:[u8;32]=kani::any();
        let mut n1=left.clone();let mut n2=right.clone();
        n1.insert(u,(c1.clone(),s1));n2.insert(u,(c2.clone(),s2));
        let (a,b)=owned31::leaf_pair(left,right,u,c1,c2,s1,s2);
        assert_eq!(a,n1);assert_eq!(b,n2);
    }
    #[kani::proof]
    #[kani::unwind(12)]
    fn folded_transition() {
        let leaves=leaves();let u:usize=kani::any();let value=bytes();let salt:[u8;32]=kani::any();
        let mut native=leaves.clone();native.insert(u,(value.clone(),salt));
        assert_eq!(native,owned31::folded_leaf(leaves,u,value,salt));
    }
    #[kani::proof]
    #[kani::unwind(12)]
    fn wide_serialization() {
        let limbs:[u32;8]=kani::any();
        // WideExact::from_limbs rejects noncanonical limbs; this constructor
        // precondition is explicit and also covers every live WideExact value.
        for limb in limbs {kani::assume(limb<aspis_core::field::P);}
        let value=E::from_limbs(limbs).unwrap();
        assert_eq!(owned31::wide_bytes(value),value.to_le_bytes());
    }

}
