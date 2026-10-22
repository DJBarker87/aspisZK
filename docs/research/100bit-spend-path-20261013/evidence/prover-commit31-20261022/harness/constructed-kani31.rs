#[cfg(kani)]
mod constructed_kani31 {
    use super::*;
    fn bytes()->Vec<u8> {
        let n:usize=kani::any();kani::assume(n<=2);
        let a:[u8;2]=kani::any();a[..n].to_vec()
    }
    fn tables()->(Table,Table) {
        let n:usize=kani::any();kani::assume(n<=2);
        let mut a=Table::new();let mut b=Table::new();
        for _ in 0..n {
            let key=bytes();let value:[u8;32]=kani::any();
            a.insert(key.clone(),value);b.insert(key,value);
        }
        (a,b)
    }
    fn same_table(x:Table,y:Table) {
        assert_eq!(x.len(),y.len());
        // Every constructed key has length <= 2. Universally choose a key
        // in that domain and a byte; map extensionality is TrustedStd.
        let key=bytes();let byte:usize=kani::any();kani::assume(byte<32);
        match (x.get(&key),y.get(&key)) {
            (None,None)=>{},(Some(a),Some(b))=>assert_eq!(a[byte],b[byte]),
            _=>panic!("different lookup"),
        }
    }
    fn same_entries(x:Vec<(Vec<u8>,[u8;32])>,y:Vec<(Vec<u8>,[u8;32])>) {
        assert_eq!(x.len(),y.len());
        if !x.is_empty() {
            let i:usize=kani::any();kani::assume(i<x.len());
            assert_eq!(x[i].0,y[i].0);
            let byte:usize=kani::any();kani::assume(byte<32);
            assert_eq!(x[i].1[byte],y[i].1[byte]);
        }
    }
    #[kani::proof]
    #[kani::unwind(12)]
    fn ordered_bytes() {
        let (t,other)=tables();
        let by_ref:Vec<_>=t.iter().map(|(k,v)|(k.clone(),*v)).collect();
        let by_value:Vec<_>=other.into_iter().collect();
        let by_owned=owned31::entries(t);
        same_entries(by_ref,by_owned.clone());same_entries(by_value,by_owned);
    }
    #[kani::proof]
    #[kani::unwind(12)]
    fn ordered_usize() {
        let n:usize=kani::any();kani::assume(n<=2);
        let mut t=BTreeMap::new();
        for _ in 0..n {let key:usize=kani::any();t.insert(key,bytes());}
        let native:Vec<_>=t.iter().map(|(k,v)|(*k,v.clone())).collect();
        assert_eq!(native,owned31::entries(t));
    }
    #[kani::proof]
    #[kani::unwind(12)]
    fn merge_transition() {
        let (t,mut native)=tables();let a=bytes();let v:[u8;32]=kani::any();
        let mut bad=false;
        if let Some(p)=native.insert(a.clone(),v) {if p!=v {bad=true;}}
        let (actual,actual_bad)=owned31::merge_step(t,a.clone(),v);
        assert_eq!(actual[&a],v);same_table(actual,native);assert_eq!(actual_bad,bad);
    }
    fn native_merge(mut table:Table,transcript:Table)->Result<Table,Error> {
        for (a,v) in transcript {if let Some(p)=table.insert(a,v) {if p!=v {return Err(Error::Transcript);}}}
        Ok(table)
    }
    #[kani::proof]
    #[kani::unwind(12)]
    fn merge_all_early_exits() {
        let (t,nt)=tables();let (tr,ntr)=tables();
        let native=native_merge(nt,ntr);
        let actual=owned31::merge(t,owned31::entries(tr));
        match (native,actual) {
            (Ok(x),Ok(y))=>same_table(x,y),
            (Err(Error::Transcript),Err(Error::Transcript))=>{},
            _=>panic!("publication status differs"),
        }
    }
    #[kani::proof]
    #[kani::unwind(12)]
    fn node_capacity() {
        let out=bytes();let nodes=bytes();let cap:usize=kani::any();kani::assume(cap<=3);
        let mut expected=out.clone();
        let reject=nodes.len()>cap;
        if !reject {expected.extend_from_slice(&nodes);expected.resize(expected.len()+cap-nodes.len(),0);}
        match owned31::append_nodes(out,nodes,cap) {
            Err(Error::Parse)=>assert!(reject),
            Ok(actual)=>{assert!(!reject);assert_eq!(actual,expected);},
            _=>panic!("unexpected error"),
        }
    }
}
