#[cfg(kani)]
mod literal_kani31 {
    use super::*;
    fn init(a:[u8;32],b:[u8;32])->Table {
        let mut t=Table::new();t.insert(vec![0],a);t.insert(vec![1],b);t
    }
    #[kani::proof] #[kani::unwind(12)]
    fn ordered() {
        let a:[u8;32]=kani::any();let b:[u8;32]=kani::any();
        let t=init(a,b);let mut iter=Vec::new();
        for (k,v) in &t {iter.push((k.clone(),*v));}
        let owned=owned31::entries(t);
        assert_eq!(iter.len(),owned.len());assert_eq!(owned.len(),2);
        let i:usize=kani::any();kani::assume(i<2);
        let byte:usize=kani::any();kani::assume(byte<32);
        assert_eq!(owned[i].0[0],i as u8);assert_eq!(iter[i].0[0],owned[i].0[0]);
        assert_eq!(iter[i].1[byte],owned[i].1[byte]);
    }
    fn transition<const KEY:u8>() {
        let a:[u8;32]=kani::any();let b:[u8;32]=kani::any();let v:[u8;32]=kani::any();
        let mut native=init(a,b);let owned=init(a,b);
        let mut bad=false;
        if let Some(p)=native.insert(vec![KEY],v) {if p!=v {bad=true;}}
        let (actual,actual_bad)=owned31::merge_step(owned,vec![KEY],v);
        assert_eq!(actual_bad,bad);assert_eq!(actual.len(),native.len());
        let byte:usize=kani::any();kani::assume(byte<32);
        assert_eq!(actual[&vec![KEY]][byte],v[byte]);
        assert_eq!(actual[&vec![0]][byte],native[&vec![0]][byte]);
        assert_eq!(actual[&vec![1]][byte],native[&vec![1]][byte]);
    }
    #[kani::proof] #[kani::unwind(12)] fn conflict(){transition::<0>()}
    #[kani::proof] #[kani::unwind(12)] fn fresh(){transition::<2>()}
}
