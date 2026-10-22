#[cfg(kani)]
mod capacity_kani31 {
    use super::*;
    fn check<const CAP:usize>() {
        let prefix:[u8;2]=kani::any();let nodes:[u8;2]=kani::any();
        let actual=owned31::append_nodes(prefix.to_vec(),nodes.to_vec(),CAP);
        if CAP<2 {
            assert!(matches!(actual,Err(Error::Parse)));
        } else {
            let out=actual.unwrap();assert_eq!(out.len(),2+CAP);
            let at:usize=kani::any();kani::assume(at<2+CAP);
            if at<2 {assert_eq!(out[at],prefix[at]);}
            else if at<4 {assert_eq!(out[at],nodes[at-2]);}
            else {assert_eq!(out[at],0);}
        }
    }
    #[kani::proof] #[kani::unwind(12)] fn oversized(){check::<1>()}
    #[kani::proof] #[kani::unwind(12)] fn exact(){check::<2>()}
    #[kani::proof] #[kani::unwind(12)] fn padded(){check::<3>()}
}
