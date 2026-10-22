
#[cfg(kani)]
mod publication32 {
    use super::owned32::*;
    use alloc::{vec,vec::Vec};
    use std::collections::BTreeMap;
    fn maps()->(IndexMap,BTreeMap<usize,Vec<u8>>) {
        let a:usize=kani::any();let b:usize=kani::any();
        let va=vec![kani::any::<u8>()];let vb=vec![kani::any::<u8>()];
        // Construct the sorted pre-state directly. This gate checks one
        // transition, rather than symbolically re-running two setup transitions.
        let xs=if a<b {vec![(a,va.clone()),(b,vb.clone())]}
            else if a==b {vec![(b,vb.clone())]}
            else {vec![(b,vb.clone()),(a,va.clone())]};
        let mut m=BTreeMap::new();m.insert(a,va);m.insert(b,vb);
        (xs,m)
    }
    #[kani::proof]
    #[kani::unwind(12)]
    fn insert_replace_order() {
        let (xs,mut m)=maps();
        let k:usize=kani::any();let v=vec![kani::any::<u8>()];
        let (ys,old)=index_insert(xs,k,v.clone(),0,Vec::new());
        let previous=m.insert(k,v);
        assert_eq!(old,previous);
        assert_eq!(ys.len(),m.len());
        // One universally selected observation proves every entry in this
        // bounded state. Avoid whole-map/vector memcmp and destructor work.
        let at:usize=kani::any();kani::assume(at<ys.len());
        let (key,value)=m.iter().nth(at).unwrap();
        assert_eq!(ys[at].0,*key);
        assert_eq!(ys[at].1.len(),value.len());
        let byte:usize=kani::any();kani::assume(byte<value.len());
        assert_eq!(ys[at].1[byte],value[byte]);
        core::mem::forget(m);core::mem::forget(ys);
    }
    #[kani::proof]
    #[kani::unwind(12)]
    fn entry_lazy() {
        let (xs,mut m)=maps();
        let k:usize=kani::any();let v=vec![kani::any::<u8>()];
        let mut invoked=false;
        m.entry(k).or_insert_with(||{invoked=true;v.clone()});
        let absent=index_absent(xs.clone(),k);
        assert_eq!(absent,invoked);
        let ys=if absent {index_insert(xs,k,v,0,Vec::new()).0}else{xs};
        assert_eq!(index_get(ys,k,0),m.get(&k).cloned());
    }
    #[kani::proof]
    #[kani::unwind(12)]
    fn lookup() {
        let (xs,m)=maps();let k:usize=kani::any();
        assert_eq!(index_get(xs,k,0),m.get(&k).cloned());
    }
    #[kani::proof]
    #[kani::unwind(16)]
    fn query_order_duplicates() {
        let k:u32=kani::any();let j:u32=kani::any();
        let a=vec![kani::any::<u8>()];let b=vec![kani::any::<u8>()];
        let (xs,_)=index_insert(Vec::new(),k as usize,a.clone(),0,Vec::new());
        let (xs,_)=index_insert(xs,j as usize,b.clone(),0,Vec::new());
        let mut m=BTreeMap::new();m.insert(k as usize,a);m.insert(j as usize,b);
        let queries=vec![k,j,k];
        let mut expected=Vec::new();
        for q in &queries {expected.extend_from_slice(&m[&(*q as usize)]);}
        assert_eq!(publish_queries(queries,xs,0,Vec::new()),Some(expected));
    }
}
