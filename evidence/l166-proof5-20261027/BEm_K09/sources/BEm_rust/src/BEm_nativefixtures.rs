include!("BEm_owned.rs");
include!("BEm_observed.rs");

// Non-vacuity of the local returned-backend class, not SHA-256 or a joint
// deployment fixture. Both actual Rust bodies execute every helper; no stubs.
#[test]
fn both_slots_success() {
    let proof=vec![0u8;compact::PROOF_BYTES];
    for ordinal in 0..2 {
        let original=RefCell::new(Vec::new());let reference=RefCell::new(Vec::new());
        let a=observed_shipped(&proof,[0;22],[[0;32];3],ordinal,Reply([0;32]),&original);
        let b=observed_reference(&proof,[0;22],[[0;32];3],ordinal,Reply([0;32]),&reference);
        assert_eq!(a,Ok(()));assert_eq!(a,b);assert_eq!(*original.borrow(),*reference.borrow());
        let expected=if ordinal==0 {84} else {90};
        assert_eq!(original.borrow().len(),expected);
        assert_eq!(original.borrow()[0].address,original.borrow()[1].address);
        assert!(original.borrow().iter().all(|a|a.returned==Some(Ok([0;32]))));
        println!("local success ordinal={ordinal} exact_attempts={expected}, full Rust Result/log equality");
    }
}
#[test]
fn both_slots_padding_rejection() {
    for ordinal in 0..2 {
        let mut proof=vec![0u8;compact::PROOF_BYTES];
        proof[compact::slot_offset(3*ordinal)+32*18]=1;
        let original=RefCell::new(Vec::new());let reference=RefCell::new(Vec::new());
        let a=observed_shipped(&proof,[0;22],[[0;32];3],ordinal,Reply([0;32]),&original);
        let b=observed_reference(&proof,[0;22],[[0;32];3],ordinal,Reply([0;32]),&reference);
        assert_eq!(a,Err(Error::Parse));assert_eq!(a,b);assert_eq!(*original.borrow(),*reference.borrow());
        let expected=if ordinal==0 {10} else {12};
        assert_eq!(original.borrow().len(),expected);
        assert_eq!(original.borrow()[0].address,original.borrow()[1].address);
        println!("local rejection ordinal={ordinal} exact_attempts={expected}, no invented parent suffix");
    }
}

// Positive and rejecting one-step executions for an actual stateful backend.
#[derive(Clone,Copy)]
struct Alternating<'a>(&'a std::cell::Cell<usize>);
impl Digest32 for Alternating<'_> {
    fn digest(&self,_:&[&[u8]])->[u8;32] { let i=self.0.get();self.0.set(i+1);[i as u8;32] }
}
#[test]
fn stateful_duplicate_rejection_prefix() {
    let proof=vec![0u8;compact::PROOF_BYTES];
    for ordinal in 0..2 {
        let ca=std::cell::Cell::new(7);let cb=std::cell::Cell::new(7);
        let la=RefCell::new(Vec::new());let lb=RefCell::new(Vec::new());
        let a=observed_shipped(&proof,[0;22],[[0;32];3],ordinal,Alternating(&ca),&la);
        let b=observed_reference(&proof,[0;22],[[0;32];3],ordinal,Alternating(&cb),&lb);
        assert_eq!(a,Err(Error::Merkle));assert_eq!(a,b);assert_eq!(*la.borrow(),*lb.borrow());
        assert_eq!(ca.get(),9);assert_eq!(cb.get(),9);assert_eq!(la.borrow().len(),2);
        assert_eq!(la.borrow()[0].returned,Some(Ok([7;32])));
        assert_eq!(la.borrow()[1].returned,Some(Ok([8;32])));
        println!("stateful duplicate rejection ordinal={ordinal}, attempts2, initial7 final9");
    }
}
