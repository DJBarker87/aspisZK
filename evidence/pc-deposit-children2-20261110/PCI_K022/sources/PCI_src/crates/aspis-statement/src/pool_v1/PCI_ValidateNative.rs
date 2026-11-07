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
include!("PCI_ValidateWindows.rs");
fn arbitrary_witness()->PoolV1PairLeafWitnessV1{
 PoolV1PairLeafWitnessV1{first_commitment:kani::any::<[u32;8]>().map(M31),second_occupied:M31(kani::any()),second_commitment:kani::any::<[u32;8]>().map(M31),second_occupancy_inverse:M31(kani::any())}
}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(digest_is_canonical,canonical_spec)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn validate_prefix(){
 let w=arbitrary_witness();let got=gates_window(&w);
 let want=if !canonical_value(&w.first_commitment)||!canonical_value(&w.second_commitment){1}else if w.second_occupied.0>=P{2}else if w.second_occupancy_inverse.0>=P{3}else{0};
 assert!((tag(got)==want)!=cfg!(PCI_NEG_VALIDATE));
}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn validate_operands(){
 let w=arbitrary_witness();let occ=w.second_occupied.0;let inv=w.second_occupancy_inverse.0;
 kani::assume(occ<P);kani::assume(inv<P);
 let got=operands_window(&w).map(|x|x.0);
 let want=[occ,if occ==0{P-1}else{occ-1},w.second_commitment[7].0,inv,if occ<=1{1-occ}else{P+1-occ},inv];
 assert!((got==want)!=cfg!(PCI_NEG_VALIDATE));
 assert!(got[0]<P&&got[1]<P&&got[3]<P&&got[4]<P&&got[5]<P);
}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn validate_after_products(){
 let w=arbitrary_witness();let product=M31(kani::any());let phase:u8=kani::any();kani::assume(phase<4);let scan:bool=kani::any();
 let got=match phase{0=>post_product0(product,w.second_occupied),1=>post_product1(product,w.second_occupied),2=>post_product2(product,w.second_occupied),_=>tail_window(&w,scan)};
 let want=match phase{0=>if product.0!=0{4}else{0},1=>if product!=w.second_occupied{5}else{0},2=>if product.0!=0{6}else{0},_=>if scan{7}else if w.second_occupied.0==1&&w.second_commitment[7].0==0{8}else{0}};
 assert!((tag(got)==want)!=cfg!(PCI_NEG_VALIDATE));
}
// Source-ordered split around the CLOSED field call; not a product stub.
fn scan_arguments(one_minus_occupied:M31,limb:M31)->[M31;2]{[one_minus_occupied,limb]}
fn scan_after_product(product:M31)->bool{product!=M31::ZERO}
#[kani::proof] #[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn validate_scan_step(){
 let words:[u32;8]=kani::any();let i:usize=kani::any();kani::assume(i<8);let one:u32=kani::any();let product:u32=kani::any();
 let mut got=scan_arguments(M31(one),M31(words[i])).map(|x|x.0);
 #[cfg(PCI_SCAN_ARG_MUTANT)]{got[1]^=1;}
 assert!((got==[one,words[i]])!=cfg!(PCI_NEG_VALIDATE));
 assert_eq!(scan_after_product(M31(product)),product!=0);
 assert!(i+1<=8);
}
