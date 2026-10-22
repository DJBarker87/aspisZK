#[derive(Clone,Copy)]
struct LengthHash<'a> {step:&'a Cell<usize>,answers:[[u8;32];3],proof:&'a[u8],public:&'a[u8],prepared:&'a Prepared,accumulator:&'a Accumulator,index:usize}
impl Digest32 for LengthHash<'_> {
 fn digest(&self,parts:&[&[u8]])->[u8;32] {
    let step=self.step.get();assert!(step<3);
    match step {
     0=>{assert_eq!(parts.len(),1);assert!(core::ptr::eq(parts[0],self.proof));},
     1=>{assert_eq!(parts.len(),1);assert!(core::ptr::eq(parts[0],self.public));},
     _=>{assert_eq!(parts.len(),2);assert_eq!(parts[0],b"UNPROVED:R1:checkpoint");assert_eq!(parts[1].len(),1736);assert_eq!(parts[1][self.index],body_byte(self.prepared,self.accumulator,&self.answers[0],&self.answers[1],self.index));}
    }
    self.step.set(step+1);self.answers[step]
 }
}
#[kani::proof]
#[kani::stub_verified(encode_k)]
#[kani::unwind(70)]
fn frozen_writer_all_bounded_lengths() {
 let p=Prepared {variant:Variant::S2,roots:kani::any(),gamma:any_e(),kappa:any_e(),alpha:[any_e(),any_e()],rho:any_k(),queries:kani::any(),semantic_alpha:core::array::from_fn(|_|any_k()),z:core::array::from_fn(|_|aspis_core::circle::SecureCirclePoint{x:any_k(),y:any_k()}),claim:any_e(),state:kani::any()};
 let a=Accumulator{weights:(0..64).map(|_|any_k()).collect(),rhs:any_e(),power:any_k(),next:10};
 let proof_storage:[u8;57_607]=kani::any();let public_storage:[u8;1880]=kani::any();
 let proof_len:usize=kani::any();let public_len:usize=kani::any();
 kani::assume(proof_len<=57_607);kani::assume(public_len<=1880);
 let proof=&proof_storage[..proof_len];let public=&public_storage[..public_len];
 let answers:[[u8;32];3]=kani::any();
 let i:usize=kani::any();kani::assume(i<1736);let j:usize=kani::any();kani::assume(j<1768);
 let step=Cell::new(0);let hash=LengthHash{step:&step,answers,proof,public,prepared:&p,accumulator:&a,index:i};
 let got=verifier::checkpoint(&p,&a,proof,public,hash);
 assert_eq!(step.get(),3);assert_eq!(got.len(),1768);
 assert_eq!(got[j],if j<1736 {body_byte(&p,&a,&answers[0],&answers[1],j)} else {answers[2][j-1736]});
}
include!("authentication-source.rs");
#[derive(Clone,Copy)]
struct ReadLengthHash<'a> {step:&'a Cell<usize>,answers:[[u8;32];3],proof:&'a[u8],public:&'a[u8],ck:&'a[u8;1768]}
impl Digest32 for ReadLengthHash<'_> {
 fn digest(&self,parts:&[&[u8]])->[u8;32] {
  let step=self.step.get();assert!(step<3);
  match step {
   0=>{assert_eq!(parts.len(),1);assert!(core::ptr::eq(parts[0],self.proof));},
   1=>{assert_eq!(parts.len(),1);assert!(core::ptr::eq(parts[0],self.public));},
   _=>{assert_eq!(parts.len(),2);assert_eq!(parts[0],b"UNPROVED:R1:checkpoint");assert!(core::ptr::eq(parts[1],&self.ck[..1736]));}
  }
  self.step.set(step+1);self.answers[step]
 }
}
#[kani::proof]
#[kani::unwind(70)]
fn reader_authentication_all_bounded_lengths() {
 let ck:[u8;1768]=kani::any();let answers:[[u8;32];3]=kani::any();
 let proof_storage:[u8;57_607]=kani::any();let public_storage:[u8;1880]=kani::any();
 let proof_len:usize=kani::any();let public_len:usize=kani::any();
 kani::assume(proof_len<=57_607);kani::assume(public_len<=1880);
 let proof=&proof_storage[..proof_len];let public=&public_storage[..public_len];
 let step=Cell::new(0);let hash=ReadLengthHash{step:&step,answers,proof,public,ck:&ck};
 let got=authenticate(&ck,proof,public,Variant::S2,hash);
 let header=&ck[..8]==b"R1P2CKP2"&&ck[8]==2&&ck[9]<=22&&ck[10]==1&&ck[11..16].iter().all(|b|*b==0);
 let mut calls=0;
 let binding=if !header {false} else {calls=1;if ck[16..48]!=answers[0] {false} else {calls=2;if ck[48..80]!=answers[1] {false} else {calls=3;ck[1736..]==answers[2]}}};
 let accepted=binding;
 assert_eq!(got,if accepted {Ok(1736)} else {Err(Error::Checkpoint)});
 assert_eq!(step.get(),calls);
}
