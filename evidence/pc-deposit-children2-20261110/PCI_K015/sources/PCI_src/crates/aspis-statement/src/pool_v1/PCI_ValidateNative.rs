use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[path="PCI_ValidateReference.rs"]mod reference;
struct Log{args:[[u32;2];3],values:[u32;3],count:usize}
fn canonical_value(d:&Digest)->bool{d[0].0<P && d[1].0<P && d[2].0<P && d[3].0<P && d[4].0<P && d[5].0<P && d[6].0<P && d[7].0<P}
fn canonical_spec(d:&Digest)->bool{
 let b:bool=kani::any();kani::assume(b==(canonical_value(d)!=cfg!(PCI_WRONG_CANON)));b
}
fn product_spec(a:M31,b:M31)->M31{
 assert!(a.0<P);assert!(b.0<P);
 let z:u32=kani::any();kani::assume(z<P);
 kani::assume(z as u64==((a.0 as u64)*(b.0 as u64))%(P as u64));M31(z)
}
fn mul_window(a:M31,b:M31,log:&mut Log)->M31{
 let out=a.mul(b);assert!(log.count<3);
 log.args[log.count]=[a.0,b.0];log.values[log.count]=out.0;log.count+=1;out
}
include!("PCI_ValidateFission.rs");
fn tag(r:Result<(),PoolV1PairLeafErrorV1>)->u8{
 use PoolV1PairLeafErrorV1::*;match r{Ok(())=>0,Err(e)=>match e{NonCanonicalCommitment=>1,NonCanonicalOccupancy=>2,NonCanonicalInverse=>3,OccupancyNotBoolean=>4,SentinelInverseMismatch=>5,EmptyInverseNonZero=>6,EmptyCommitmentNonZero=>7,OccupiedSentinelZero=>8,SelectedSlotEmpty=>9}}
}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(M31::mul,product_spec)]
#[kani::stub(digest_is_canonical,canonical_spec)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn validate_prefix(){
 let w=PoolV1PairLeafWitnessV1{first_commitment:kani::any::<[u32;8]>().map(M31),second_occupied:M31(kani::any()),second_commitment:kani::any::<[u32;8]>().map(M31),second_occupancy_inverse:M31(kani::any())};
 let scan:bool=kani::any();let mut log=Log{args:[[0;2];3],values:[0;3],count:0};
 let got=validate_fission(&w,scan,&mut log);
 let want=reference::prefix(canonical_value(&w.first_commitment),canonical_value(&w.second_commitment),w.second_occupied.0,w.second_occupancy_inverse.0,w.second_sentinel().0,log.values,scan);
 assert!((tag(got)==want)!=cfg!(PCI_NEG_VALIDATE));
 let admitted=canonical_value(&w.first_commitment)&&canonical_value(&w.second_commitment)&&w.second_occupied.0<P&&w.second_occupancy_inverse.0<P;
 if admitted{
  let occ=w.second_occupied.0;let inv=w.second_occupancy_inverse.0;
  assert_eq!(log.args[0],[occ,if occ==0{P-1}else{occ-1}]);
  let count=if log.values[0]!=0{1}else if log.values[1]!=occ{2}else{3};assert_eq!(log.count,count);
  if count>1{assert_eq!(log.args[1],[w.second_sentinel().0,inv]);}
  if count>2{assert_eq!(log.args[2],[if occ<=1{1-occ}else{P+1-occ},inv]);}
 }else{assert_eq!(log.count,0);}
}
// Exactly one application of the frozen Iterator.any predicate, at arbitrary cursor.
fn scan_window(one_minus_occupied:M31,limb:M31,log:&mut Log)->bool{
 mul_window(one_minus_occupied,limb,log)!=M31::ZERO
}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(M31::mul,product_spec)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn validate_scan_step(){
 let words:[u32;8]=kani::any();let i:usize=kani::any();kani::assume(i<8);
 let one:u32=kani::any();kani::assume(one<P);kani::assume(words[i]<P);
 let mut log=Log{args:[[0;2];3],values:[0;3],count:0};
 let got=scan_window(M31(one),M31(words[i]),&mut log);
 assert_eq!(log.count,1);assert_eq!(log.args[0],[one,words[i]]);
 assert!((got==(log.values[0]!=0))!=cfg!(PCI_NEG_VALIDATE));
 assert!(i+1<=8);
}
