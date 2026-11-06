use super::*;
pub(super) fn reference(p:PlannedPairForestNullifierMarkerV1)->NullifierMarkerPreparationV1 {p.preparation}
#[kani::proof_for_contract(PlannedPairForestNullifierMarkerV1::preparation)]
fn contract(){let p:PlannedPairForestNullifierMarkerV1=kani::any();let _=p.preparation();}
#[kani::ensures(|_|true)]
fn weak(x:bool)->NullifierMarkerPreparationV1 {if x {NullifierMarkerPreparationV1::PopulateProgramOwnedZeroed}else{NullifierMarkerPreparationV1::CreateOrAllocateSystemOwned}}
#[kani::proof_for_contract(weak)] fn weak_contract(){let _=weak(kani::any());}
#[kani::proof] fn real(){let x:bool=kani::any();assert_eq!(weak(x),if x {NullifierMarkerPreparationV1::PopulateProgramOwnedZeroed}else{NullifierMarkerPreparationV1::CreateOrAllocateSystemOwned});}
#[kani::proof] #[kani::stub_verified(weak)] fn unimplied(){let x:bool=kani::any();assert_eq!(weak(x),if x {NullifierMarkerPreparationV1::PopulateProgramOwnedZeroed}else{NullifierMarkerPreparationV1::CreateOrAllocateSystemOwned});}
#[kani::modifies(&mut x[0])] #[kani::ensures(|_|true)]
fn bad_frame(x:&mut [u8;2])->NullifierMarkerPreparationV1 {x[1]=x[1].wrapping_add(1);NullifierMarkerPreparationV1::PopulateProgramOwnedZeroed}
#[kani::proof_for_contract(bad_frame)]fn frame(){let mut x:[u8;2]=kani::any();let _=bad_frame(&mut x);}
