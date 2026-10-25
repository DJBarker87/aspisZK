#![allow(static_mut_refs)]
use super::{Prepared,View,Error};
use alloc::boxed::Box;
use aspis_core::{Digest32,field::{WideExact as E,QM31,CM31,M31},circle::SecureCirclePoint};
use crate::{transport::Variant,r1_semantic::Verified};

#[derive(Clone,Copy)]struct Hash;
impl Digest32 for Hash{fn digest(&self,parts:&[&[u8]])->[u8;32]{unsafe{digest_step(parts)}}}
static mut DIGEST_CALLS:usize=0;
static mut HASHES:[[u8;32];33]=[[0;32];33];
static mut STAGE:usize=0;
static mut MUL_CALLS:usize=0;
static mut FAIL_AT:u8=2;
static mut ERROR:Error=Error::Parse;
static mut STATES:[[u8;32];7]=[[0;32];7];
static mut SEM_STATE:[u8;32]=[0;32];
static mut SCALARS:[E;4]=[E::ZERO;4];
static mut POWERS:[E;29]=[E::ZERO;29];
static mut QUERY:[u32;22]=[0;22];
static mut RHO:QM31=QM31::ZERO;
static mut CLAIM:E=E::ZERO;
static mut INACTIVE:E=E::ZERO;
static mut SEM_PTR:*const ()=core::ptr::null();
static mut G_PTR:*const [E;29]=core::ptr::null();
static mut Y1_PTR:*const u8=core::ptr::null();
static mut ROUND0_PTR:*const u8=core::ptr::null();
static mut FINAL_PTR:*const u8=core::ptr::null();
static mut FOLDED:[u8;32]=[0;32];
static mut ROUND1:[u8;224]=[0;224];
fn same_bytes(a:&[u8],b:&[u8]){assert!(a.len()==b.len());let mut i=0;while i<a.len(){assert!(a[i]==b[i]);i+=1;}}
fn same_e(a:E,b:E){let a=a.to_limbs();let b=b.to_limbs();let mut i=0;while i<8{assert!(a[i]==b[i]);i+=1;}}
fn same_q(a:QM31,b:QM31){assert!(a.c0.a==b.c0.a);assert!(a.c0.b==b.c0.b);assert!(a.c1.a==b.c1.a);assert!(a.c1.b==b.c1.b);}
fn same_powers(a:&[E;29],b:&[E;29]){let mut i=0;while i<29{same_e(a[i],b[i]);i+=1;}}

// Exact digest preimages are checked in actual execution order, including all
// eight query squeeze/advance pairs before a sampler error can be returned.
unsafe fn digest_step(parts:&[&[u8]])->[u8;32]{
 let n=DIGEST_CALLS;assert!(n<33);
 if n==0{
  assert!(STAGE==0);assert!(parts.len()==3);
  same_bytes(parts[0],b"UNPROVED:R1:PRIVATE-SALTED:P3");
  same_bytes(parts[1],&[2]);same_bytes(parts[2],&SEM_STATE);STAGE=1;
 }else if n<13{
  let row=(n-1)/3;let step=(n-1)%3;assert!(STAGE==row+1);
  let base=1+3*row;
  if step==0{
   assert!(parts.len()==4);same_bytes(parts[0],&HASHES[base-1]);
   same_bytes(parts[1],&[0,0xa0+27+row as u8]);
   let len=match row{0=>928u32,1=>32,2=>224,_=>256};
   same_bytes(parts[2],&len.to_le_bytes());assert!(parts[3].len()==len as usize);
   match row{
    0=>assert!(parts[3].as_ptr()==Y1_PTR),
    1=>same_bytes(parts[3],&INACTIVE.to_le_bytes()),
    2=>assert!(parts[3].as_ptr()==ROUND0_PTR),
    _=>{same_bytes(&parts[3][..32],&FOLDED);same_bytes(&parts[3][32..],&ROUND1);}
   }
  }else{
   assert!(parts.len()==2);same_bytes(parts[0],&HASHES[base]);
   same_bytes(parts[1],&[step as u8]);
  }
 }else if n<30{
  assert!(STAGE==5);
  if n==13{
   assert!(parts.len()==4);same_bytes(parts[0],&HASHES[12]);
   same_bytes(parts[1],&[0,0xa0+31]);same_bytes(parts[2],&2048u32.to_le_bytes());
   assert!(parts[3].len()==2048);assert!(parts[3].as_ptr()==FINAL_PTR);
  }else{
   let k=(n-14)/2;let step=(n-14)%2;
   assert!(parts.len()==2);same_bytes(parts[0],&HASHES[13+2*k]);
   same_bytes(parts[1],&[1+step as u8]);
  }
 }else{
  assert!(STAGE==6);let step=n-30;
  if step==0{
   assert!(parts.len()==4);same_bytes(parts[0],&STATES[5]);
   same_bytes(parts[1],&[0,0xa0+32]);same_bytes(parts[2],&0u32.to_le_bytes());
   assert!(parts[3].is_empty());
  }else{
   assert!(parts.len()==2);same_bytes(parts[0],&HASHES[30]);
   same_bytes(parts[1],&[step as u8]);
  }
 }
 DIGEST_CALLS=n+1;HASHES[n]
}
fn gamma_stub(block:&[u8;32])->E{unsafe{
 assert!(STAGE==1);assert!(DIGEST_CALLS==4);same_bytes(block,&HASHES[2]);
 STAGE=2;SCALARS[0]
}}
fn ordinary_stub(block:&[u8;32])->E{unsafe{
 let n=STAGE;assert!(n>=2&&n<=4);assert!(DIGEST_CALLS==1+3*n);
 same_bytes(block,&HASHES[3*n-1]);STAGE=n+1;SCALARS[n-1]
}}
fn qm_stub(block:&[u8;32])->QM31{unsafe{
 assert!(STAGE==6);assert!(DIGEST_CALLS==33);same_bytes(block,&HASHES[31]);
 STAGE=7;RHO
}}
fn pairs_stub(blocks:&[[u8;32];8],advances:&[[u8;32];8])
 ->Result<([u32;22],[u8;32]),aspis_core::transcript::QuerySampleError>{unsafe{
 assert!(STAGE==5);assert!(DIGEST_CALLS==30);
 let mut k=0;while k<8{
  same_bytes(&blocks[k],&HASHES[14+2*k]);same_bytes(&advances[k],&HASHES[15+2*k]);k+=1;
 }
 STAGE=6;
 if FAIL_AT==0{Err(aspis_core::transcript::QuerySampleError::DrawLimitExhausted{accepted:0,max_draws:64})}
 else{Ok((QUERY,STATES[5]))}
}}
// Only a primitive multiplication normal-return boundary remains here.
// The complete frozen weights::powers body actually executes in Prepared::new.
fn mul_stub(left:E,right:E)->E{unsafe{
 let n=MUL_CALLS;assert!(STAGE==7);assert!(n<28);
 same_e(left,POWERS[n]);same_e(right,SCALARS[0]);
 MUL_CALLS=n+1;if MUL_CALLS==28{STAGE=8;}POWERS[n+1]
}}
fn claim_stub<H:Digest32>(sem:&Verified<H>,y1:&[u8],inactive:E,g:&[E;29],kappa:E)->Result<E,Error>{unsafe{
 assert!(STAGE==8);assert!(MUL_CALLS==28);assert!(sem as *const Verified<H> as *const ()==SEM_PTR);
 assert!(y1.len()==928);assert!(y1.as_ptr()==Y1_PTR);same_e(inactive,INACTIVE);
 assert!(g as *const [E;29]==G_PTR);same_powers(g,&POWERS);same_e(kappa,SCALARS[1]);STAGE=9;
 if FAIL_AT==1{Err(ERROR)}else{Ok(CLAIM)}
}}
fn any_q()->QM31{QM31{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}}}
fn any_row()->[QM31;29]{let mut row=[QM31::ZERO;29];let mut i=0;while i<29{row[i]=any_q();i+=1;}row}
fn any_challenges()->crate::r1_wire::Challenges{let mut zc=[QM31::ZERO;10];let mut i=0;while i<10{zc[i]=any_q();i+=1;}crate::r1_wire::Challenges{lambda:any_q(),chi:any_q(),theta:any_q(),zc,mu:any_q(),eta:any_q()}}
fn any_e()->E{let mut words=[0u32;8];let mut i=0;while i<8{let x=kani::any::<u32>()&0x7fff_ffff;words[i]=if x==0x7fff_ffff{0}else{x};i+=1;}match E::from_limbs(words){Some(e)=>e,None=>{assert!(false);E::ZERO}}}
fn any_es<const N:usize>()->[E;N]{let mut out=[E::ZERO;N];let mut i=0;while i<N{out[i]=any_e();i+=1;}out}
fn any_error()->Error{match kani::any::<u8>()%8{0=>Error::Parse,1=>Error::Semantic,2=>Error::Transcript,3=>Error::Relation,4=>Error::Merkle,5=>Error::Query,6=>Error::Checkpoint,_=>Error::Allocation}}

#[kani::proof]
#[kani::unwind(257)]
#[kani::stub(crate::sampler::gamma_sample,gamma_stub)]
#[kani::stub(crate::sampler::ordinary_sample,ordinary_stub)]
#[kani::stub(crate::sampler::qm31_sample,qm_stub)]
#[kani::stub(aspis_core::r0_transcript::queries_from_pairs,pairs_stub)]
#[kani::stub(aspis_core::field::WideExact::mul,mul_stub)]
#[kani::stub(crate::verifier::prepared_claim,claim_stub)]
fn prepared_new_s2_native_transcript(){
 let mut alpha=[QM31::ZERO;10];let mut i=0;while i<10{alpha[i]=any_q();i+=1;}
 let roots=kani::any::<[[u8;32];2]>();
 let z=[SecureCirclePoint{x:any_q(),y:any_q()},SecureCirclePoint{x:any_q(),y:any_q()}];
 let semantic_state=kani::any::<[u8;32]>();
 let sem=Verified{roots,challenges:any_challenges(),
  alpha,claims:Box::new([any_row(),any_row(),any_row()]),extra:any_row(),before_z1:any_row(),state_before_z0:kani::any(),z,
  transcript:crate::r1_wire::SemanticTranscript::proof_input(Hash,semantic_state,kani::any())};
 let y1=kani::any::<[u8;928]>();let round0=kani::any::<[u8;224]>();let round1=kani::any::<[u8;224]>();let folded=kani::any::<[u8;32]>();let final_message=kani::any::<[u8;2048]>();
 let inactive=any_e();let view=View{variant:Variant::S2,semantic:&[],y1:&y1,inactive,round0:&round0,folded_root:Some(&folded),round1:&round1,final_message:&final_message,query_bytes:&[]};
 let mut scratch=any_es::<29>();let initial=scratch;
 let scalars=any_es::<4>();let mut powers=any_es::<29>();powers[0]=E::ONE;let claim=any_e();let rho=any_q();let queries=kani::any::<[u32;22]>();let hashes=kani::any::<[[u8;32];33]>();let selected=(kani::any::<u8>()%8) as usize;let states=[hashes[0],hashes[3],hashes[6],hashes[9],hashes[12],hashes[15+2*selected],hashes[32]];let fail_at=kani::any::<u8>()%3;let error=any_error();
 unsafe{DIGEST_CALLS=0;HASHES=hashes;STAGE=0;MUL_CALLS=0;FAIL_AT=fail_at;ERROR=error;STATES=states;SEM_STATE=semantic_state;SCALARS=scalars;POWERS=powers;QUERY=queries;RHO=rho;CLAIM=claim;INACTIVE=inactive;
  SEM_PTR=&sem as *const Verified<Hash> as *const ();G_PTR=&scratch;Y1_PTR=y1.as_ptr();ROUND0_PTR=round0.as_ptr();FINAL_PTR=final_message.as_ptr();FOLDED=folded;ROUND1=round1;}
 let result=Prepared::new(&sem,&view,Hash,&mut scratch);
 assert!(unsafe{DIGEST_CALLS}==if fail_at==0{30}else{33});
 if fail_at==0{same_powers(&scratch,&initial);assert!(unsafe{STAGE}==6);assert!(unsafe{MUL_CALLS}==0);}else{same_powers(&scratch,&powers);assert!(unsafe{STAGE}==9);assert!(unsafe{MUL_CALLS}==28);}
 match result{
  Err(actual)=>{assert!(fail_at<2);assert!(actual==if fail_at==0{Error::Transcript}else{error});}
  Ok(out)=>{assert!(fail_at==2);assert!(out.variant==Variant::S2);let mut p=0;while p<2{same_bytes(&out.roots[p],&roots[p]);same_q(out.z[p].x,z[p].x);same_q(out.z[p].y,z[p].y);p+=1;}
   same_e(out.gamma,scalars[0]);same_e(out.kappa,scalars[1]);same_e(out.alpha[0],scalars[2]);same_e(out.alpha[1],scalars[3]);same_q(out.rho,rho);same_e(out.claim,claim);same_bytes(&out.state,&states[6]);
   i=0;while i<22{assert!(out.queries[i]==queries[i]);i+=1;}i=0;while i<10{same_q(out.semantic_alpha[i],alpha[i]);i+=1;}
  }
 }
 kani::cover!(fail_at==0,"query error preserves incoming scratch");
 kani::cover!(fail_at==1,"claim error preserves actual early-helper powers");
 kani::cover!(fail_at==2,"complete native Prepared return and reused scratch");
}

// Excluded negative control: same values, wrong caller scratch address.
