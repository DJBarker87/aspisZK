use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn canonical(d:[u32;8])->bool{d[0]<P && d[1]<P && d[2]<P && d[3]<P && d[4]<P && d[5]<P && d[6]<P && d[7]<P}
// Assertions establish the call-site specialization from the ACTUAL parent's constructor.
// PCI_SingleValidation.validation proves this is the exact CLOSED223 law on this shape.
fn validate_spec(w:&PoolV1PairLeafWitnessV1)->Result<(),PoolV1PairLeafErrorV1>{
 assert_eq!(w.second_occupied,M31::ZERO);assert_eq!(w.second_occupancy_inverse,M31::ZERO);
 assert_eq!(w.second_commitment,[M31::ZERO;8]);
 let ok:bool=kani::any();
 kani::assume(ok==(canonical(w.first_commitment.map(|x|x.0))!=cfg!(PCI_SINGLE_SPEC_MUTANT)));
 if ok{Ok(())}else{Err(PoolV1PairLeafErrorV1::NonCanonicalCommitment)}
}
#[kani::proof] #[kani::unwind(100)]
#[kani::stub(PoolV1PairLeafWitnessV1::validate,validate_spec)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn single_output(){
 let d:[u32;8]=kani::any();let mut input=d.map(M31);
 #[cfg(PCI_SINGLE_ARG_MUTANT)]{input[0].0^=1;}
 let got=PoolV1PairLeafWitnessV1::single_output(input);
 let same=match got{
  Ok(w)=>canonical(d)&&w.first_commitment.map(|x|x.0)==d&&w.second_occupied==M31::ZERO&&w.second_occupancy_inverse==M31::ZERO&&w.second_commitment==[M31::ZERO;8],
  Err(e)=>!canonical(d)&&e==PoolV1PairLeafErrorV1::NonCanonicalCommitment
 };
 assert!(same!=cfg!(PCI_NEG_SINGLE));
}
