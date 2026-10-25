// These are native value/control checks under Kani's allocator model.
// They are NOT a universal OOM/abort or ordered oracle-event theorem.
#[kani::proof]
#[kani::unwind(260)]
fn Port20ALLOC_constructor_all_variants() {
    use crate::{field::{QM31,WideExact},transport::Variant,verifier::{Accumulator,Error}};
    let v=match kani::any::<u8>() % 3 { 0=>Variant::S1, 1=>Variant::S2, _=>Variant::D };
    match Accumulator::new(v) {
        Ok(a)=>{
            assert_eq!(a.weights.len(),v.final_len());
            for x in &a.weights { assert_eq!(*x,QM31::ZERO); }
            assert_eq!(a.rhs,WideExact::ZERO);
            assert_eq!(a.power,QM31::ONE);
            assert_eq!(a.next,0);
        },
        Err(e)=>assert_eq!(e,Error::Allocation),
    }
}

#[kani::proof]
#[kani::unwind(3)]
fn Port20ALLOC_real_capacity_errors() {
    use crate::field::{QM31,CM31,M31};
    let limbs:[u32;4]=kani::any();
    let q=QM31{c0:CM31{a:M31(limbs[0]),b:M31(limbs[1])},c1:CM31{a:M31(limbs[2]),b:M31(limbs[3])}};
    // These are real capacity-overflow Err paths, not allocator OOM evidence.
    let qr=crate::r0::heap::filled(usize::MAX,q);
    let rr=crate::r0::heap::filled(usize::MAX,kani::any::<[u64;4]>());
    assert!(matches!(qr,Err(crate::r0::Error::Allocation)));
    assert!(matches!(rr,Err(crate::r0::Error::Allocation)));
}
