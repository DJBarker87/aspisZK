#[cfg(kani)]
mod publication_kani31 {
    use super::*;
    fn bytes()->Vec<u8> {
        let n:usize=kani::any();kani::assume(n<=2);
        let a:[u8;2]=kani::any();a[..n].to_vec()
    }
    fn table()->Table {
        let n:usize=kani::any();kani::assume(n<=3);
        let mut t=Table::new();
        for _ in 0..n {t.insert(bytes(),kani::any());}t
    }
    #[kani::proof]
    #[kani::unwind(12)]
    fn ordered_bytes() {
        let t=table();
        let by_ref:Vec<_>=t.iter().map(|(k,v)|(k.clone(),*v)).collect();
        let by_value:Vec<_>=t.clone().into_iter().collect();
        let by_owned=owned31::entries(t);
        assert_eq!(by_ref,by_owned);assert_eq!(by_value,by_owned);
    }
    #[kani::proof]
    #[kani::unwind(12)]
    fn ordered_usize() {
        let n:usize=kani::any();kani::assume(n<=3);
        let mut t=BTreeMap::new();
        for _ in 0..n {let key:usize=kani::any();t.insert(key,bytes());}
        let native:Vec<_>=t.iter().map(|(k,v)|(*k,v.clone())).collect();
        assert_eq!(native,owned31::entries(t));
    }
    #[kani::proof]
    #[kani::unwind(12)]
    fn merge_transition() {
        let t=table();let a=bytes();let v:[u8;32]=kani::any();
        let mut native=t.clone();
        let mut bad=false;
        if let Some(p)=native.insert(a.clone(),v) {if p!=v {bad=true;}}
        let (actual,actual_bad)=owned31::merge_step(t,a.clone(),v);
        assert_eq!(actual,native);assert_eq!(actual_bad,bad);
        assert_eq!(actual[&a],v);
    }
    fn native_merge(mut table:Table,transcript:Table)->Result<Table,Error> {
        for (a,v) in transcript {if let Some(p)=table.insert(a,v) {if p!=v {return Err(Error::Transcript);}}}
        Ok(table)
    }
    #[kani::proof]
    #[kani::unwind(12)]
    fn merge_all_early_exits() {
        let t=table();let tr=table();
        let native=native_merge(t.clone(),tr.clone());
        let actual=owned31::merge(t,owned31::entries(tr));
        match (native,actual) {
            (Ok(x),Ok(y))=>assert_eq!(x,y),
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
