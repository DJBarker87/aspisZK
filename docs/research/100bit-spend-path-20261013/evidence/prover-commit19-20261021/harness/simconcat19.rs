#[cfg(kani)]
mod simconcat19 {
    use super::*;
    #[kani::proof]
    #[kani::unwind(18)]
    fn three_slices() {
        let a:[u8;4]=kani::any();
        let b:[u8;4]=kani::any();
        let c:[u8;4]=kani::any();
        let na:usize=kani::any();let nb:usize=kani::any();let nc:usize=kani::any();
        kani::assume(na<=4);kani::assume(nb<=4);kani::assume(nc<=4);
        let parts=[&a[..na],&b[..nb],&c[..nc]];
        let actual=concat(&parts);
        let expected=owned19::concat(vec![a[..na].to_vec(),b[..nb].to_vec(),c[..nc].to_vec()],0,vec![]);
        assert_eq!(actual,expected);
    }
}
