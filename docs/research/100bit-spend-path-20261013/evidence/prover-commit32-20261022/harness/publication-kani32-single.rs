// Smallest native transition gate. This covers empty/singleton pre-states;
// the general recursion is established separately by the Lean list proofs.
#[cfg(kani)]
mod transition32 {
    use super::owned32::*;
    use alloc::{vec,vec::Vec};
    use std::collections::BTreeMap;
    fn one()->(IndexMap,BTreeMap<usize,Vec<u8>>) {
        let key:usize=kani::any();let value=vec![kani::any::<u8>()];
        let empty:bool=kani::any();
        let mut m=BTreeMap::new();
        if empty {(Vec::new(),m)} else {
            m.insert(key,value.clone());(vec![(key,value)],m)
        }
    }
    fn same(xs:IndexMap,m:BTreeMap<usize,Vec<u8>>) {
        assert_eq!(xs.len(),m.len());
        if !xs.is_empty() {
            let at:usize=kani::any();kani::assume(at<xs.len());
            let (key,value)=m.iter().nth(at).unwrap();
            assert_eq!(xs[at].0,*key);
            assert_eq!(xs[at].1.len(),value.len());
            assert_eq!(xs[at].1[0],value[0]);
        }
        core::mem::forget(m);core::mem::forget(xs);
    }
    #[kani::proof]
    #[kani::unwind(12)]
    fn insert_replace_order() {
        let (xs,mut m)=one();let key:usize=kani::any();let value=vec![kani::any::<u8>()];
        let (next,old)=index_insert(xs,key,value.clone(),0,Vec::new());
        let expected=m.insert(key,value);
        assert_eq!(old,expected);same(next,m);
    }
    #[kani::proof]
    #[kani::unwind(12)]
    fn entry_lazy() {
        let (xs,mut m)=one();let key:usize=kani::any();let value=vec![kani::any::<u8>()];
        let mut invoked=false;
        m.entry(key).or_insert_with(||{invoked=true;value.clone()});
        let absent=index_absent(xs.clone(),key);assert_eq!(absent,invoked);
        let next=if absent {index_insert(xs,key,value,0,Vec::new()).0}else{xs};
        same(next,m);
    }
    #[kani::proof]
    #[kani::unwind(12)]
    fn lookup() {
        let (xs,m)=one();let key:usize=kani::any();
        assert_eq!(index_get(xs,key,0),m.get(&key).cloned());
        core::mem::forget(m);
    }
}
