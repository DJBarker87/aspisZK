include!("BEl_owned.rs");

// Non-vacuity of the local returned-backend class, not SHA-256 or a joint
// deployment fixture. Both actual Rust bodies execute every helper; no stubs.
#[test]
fn both_slots_success() {
    let proof=vec![0u8;compact::PROOF_BYTES];
    for ordinal in 0..2 {
        let original=RefCell::new(Vec::new());let reference=RefCell::new(Vec::new());
        let a=shipped::batch_merkle_values(&proof,[0;22],[[0;32];3],ordinal,Recording{backend:Reply([0;32]),log:&original});
        let b=batch(&proof,[0;22],[[0;32];3],ordinal,Recording{backend:Reply([0;32]),log:&reference});
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
        let a=shipped::batch_merkle_values(&proof,[0;22],[[0;32];3],ordinal,Recording{backend:Reply([0;32]),log:&original});
        let b=batch(&proof,[0;22],[[0;32];3],ordinal,Recording{backend:Reply([0;32]),log:&reference});
        assert_eq!(a,Err(Error::Parse));assert_eq!(a,b);assert_eq!(*original.borrow(),*reference.borrow());
        let expected=if ordinal==0 {10} else {12};
        assert_eq!(original.borrow().len(),expected);
        assert_eq!(original.borrow()[0].address,original.borrow()[1].address);
        println!("local rejection ordinal={ordinal} exact_attempts={expected}, no invented parent suffix");
    }
}
