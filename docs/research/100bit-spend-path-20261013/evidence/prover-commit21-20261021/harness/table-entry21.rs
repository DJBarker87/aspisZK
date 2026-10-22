// One owned table entry; prefix traversal is composed by Lean, not unwound.
// This is the source-shaped owned reference, not std::BTreeMap internals.
#[cfg(kani)]
mod table_entry21 {
    #[kani::ensures(|result| *result == (left == right))]
    fn key_equal(left:[u8;4],right:[u8;4])->bool { left==right }

    #[kani::proof_for_contract(key_equal)]
    #[kani::unwind(5)]
    fn key_comparison() { key_equal(kani::any(),kani::any()); }

    #[kani::proof]
    #[kani::stub_verified(key_equal)]
    #[kani::unwind(34)]
    fn entry_with_symbolic_prefix() {
        let key:[u8;4]=kani::any();let address:[u8;4]=kani::any();
        let previous:[u8;32]=kani::any();let answer:[u8;32]=kani::any();
        // The prefix is summarized by its first hit; None means traversal
        // reaches this entry. No bound on the length of that prefix is used.
        let prefix:Option<[u8;32]>=kani::any();
        let suffix:Option<[u8;32]>=kani::any();
        let collision:bool=kani::any();
        let same=key_equal(key,address);
        let old=match prefix {Some(v)=>Some(v),None=>if same {Some(previous)} else {suffix}};
        let mut flag=collision;
        if let Some(prev)=old { if prev!=answer {flag=true;} }
        assert_eq!(flag,collision || old.map(|v|v!=answer).unwrap_or(false));
        let selected=match prefix {Some(v)=>Some(v),None=>if key==address {Some(previous)} else {suffix}};
        assert_eq!(old,selected);
    }
}
