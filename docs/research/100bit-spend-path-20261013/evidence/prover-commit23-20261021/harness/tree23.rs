#[cfg(kani)]
mod tree23 {
    use super::*;
    // Operation-split source gates. These cover a leaf node, not arbitrary
    // node height. The universal TreeMap model is a separate Lean spec.
    #[kani::proof]
    #[kani::unwind(34)]
    fn insert() {
        let old_key:u8=kani::any();let key:u8=kani::any();
        let old:[u8;32]=kani::any();let answer:[u8;32]=kani::any();
        let at:usize=kani::any();kani::assume(at<32);
        let mut table=Table::new();table.insert(vec![old_key],old);
        let previous=table.insert(vec![key],answer);
        assert_eq!(previous.map(|v|v[at]),if key==old_key {Some(old[at])} else {None});
        assert_eq!(table.len(),if key==old_key {1} else {2});
    }
    #[kani::proof]
    #[kani::unwind(34)]
    fn get() {
        let key:u8=kani::any();let query:u8=kani::any();let answer:[u8;32]=kani::any();
        let at:usize=kani::any();kani::assume(at<32);
        let mut table=Table::new();table.insert(vec![key],answer);
        assert_eq!(table.get(&vec![query]).map(|v|v[at]),if query==key {Some(answer[at])} else {None});
        assert_eq!(table.len(),1);
    }
    #[kani::proof]
    #[kani::unwind(34)]
    fn iter_step() {
        let key:u8=kani::any();let answer:[u8;32]=kani::any();
        let at:usize=kani::any();kani::assume(at<32);
        let mut table=Table::new();table.insert(vec![key],answer);
        let mut iter=table.iter();let entry=iter.next().unwrap();
        assert_eq!(entry.0.len(),1);assert_eq!(entry.0[0],key);assert_eq!(entry.1[at],answer[at]);
        assert!(iter.next().is_none());
    }
}
