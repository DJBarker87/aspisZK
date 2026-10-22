#[cfg(kani)]
mod tree22 {
    use super::*;
    // Exact shipped map/key/value types; one existing entry and one insert.
    // This checks call semantics for this shape, not an arbitrary tree height.
    #[kani::proof]
    #[kani::unwind(34)]
    fn insert_get() {
        let old_key:u8=kani::any(); let key:u8=kani::any(); let query:u8=kani::any();
        let old:[u8;32]=kani::any();let answer:[u8;32]=kani::any();
        let mut table=Table::new();table.insert(vec![old_key],old);
        let previous=table.insert(vec![key],answer);
        assert_eq!(previous,if key==old_key {Some(old)} else {None});
        let got=table.get(&vec![query]).copied();
        assert_eq!(got,if query==key {Some(answer)} else if query==old_key {Some(old)} else {None});
        assert_eq!(table.len(),if key==old_key {1} else {2});
    }
    #[kani::proof]
    #[kani::unwind(34)]
    fn enumerate() {
        let a:u8=kani::any();let b:u8=kani::any();
        let av:[u8;32]=kani::any();let bv:[u8;32]=kani::any();
        let mut table=Table::new();table.insert(vec![a],av);table.insert(vec![b],bv);
        let mut it=table.iter();let first=it.next().unwrap();
        if a<b {
            assert_eq!(*first.0,vec![a]);assert_eq!(*first.1,av);
            let second=it.next().unwrap();assert_eq!(*second.0,vec![b]);assert_eq!(*second.1,bv);
        } else if a>b {
            assert_eq!(*first.0,vec![b]);assert_eq!(*first.1,bv);
            let second=it.next().unwrap();assert_eq!(*second.0,vec![a]);assert_eq!(*second.1,av);
        } else {assert_eq!(*first.0,vec![b]);assert_eq!(*first.1,bv);}
        assert!(it.next().is_none());
    }
}
