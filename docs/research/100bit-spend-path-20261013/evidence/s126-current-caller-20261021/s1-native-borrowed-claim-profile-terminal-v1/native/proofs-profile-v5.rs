#![allow(static_mut_refs)]
use super::Error;
use alloc::boxed::Box;
use aspis_core::{Digest32,field::{WideExact as E,QM31,CM31,M31},circle::SecureCirclePoint};
use crate::r1_semantic::Verified;
#[derive(Clone,Copy)]struct Hash;
impl Digest32 for Hash {fn digest(&self,_:&[&[u8]])->[u8;32]{panic!("claim must not read Digest32")}}
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
static mut STOP:usize=174;
static mut CPUSH:usize=0;
static mut CFINISH:usize=0;
static mut CFIELD:usize=0;
static mut CADD:usize=0;
static mut KG:[E;7]=[E::ZERO;7];
static mut DOT_RET:[E;6]=[E::ZERO;6];
static mut FIELDS:[E;29]=[E::ZERO;29];
static mut MULTS:[E;7]=[E::ZERO;7];
static mut ADDS:[E;7]=[E::ZERO;7];
static mut DOT_WORDS:[[u64;8];174]=[[0;8];174];
static mut DOT_COUNTS:[usize;174]=[0;174];
static mut INACTIVE:E=E::ZERO;
static mut SEM_PTR:*const ()=core::ptr::null();
static mut G_PTR:*const [E;29]=core::ptr::null();
static mut Y1_PTR:*const u8=core::ptr::null();
static mut ROUND0_PTR:*const u8=core::ptr::null();
static mut FINAL_PTR:*const u8=core::ptr::null();
static mut FOLDED:[u8;32]=[0;32];
static mut ROUND1:[u8;224]=[0;224];

fn same_e(a:E,b:E){let a=a.to_limbs();let b=b.to_limbs();let mut i=0;while i<8{assert!(a[i]==b[i]);i+=1;}}

fn same_q(a:QM31,b:QM31){assert!(a.c0.a==b.c0.a);assert!(a.c0.b==b.c0.b);assert!(a.c1.a==b.c1.a);assert!(a.c1.b==b.c1.b);}

fn mul_stub(left:E,right:E)->E{unsafe{
 let n=MUL_CALLS;
 let out=if n<28{
  assert!(STAGE==7);same_e(left,POWERS[n]);same_e(right,SCALARS[0]);
  if n==27{STAGE=8;}POWERS[n+1]
 }else if n<34{
  assert!(STAGE==8);let k=n-28;same_e(left,KG[k]);same_e(right,SCALARS[1]);
  if n==33{STAGE=9;}KG[k+1]
 }else{
  assert!(STAGE==10);assert!(n<41);let k=n-34;assert!(CADD==k);
  same_e(left,KG[k]);same_e(right,if k==0{INACTIVE}else{DOT_RET[k-1]});MULTS[k]
 };
 MUL_CALLS=n+1;out
}}

fn same_dot(dot:&crate::fast_pairing::EbyKDot,n:usize){unsafe{
 let (words,count)=dot.proof_words();let mut i=0;
 while i<8{assert!(words[i]==if n%29==0{0}else{DOT_WORDS[n-1][i]});i+=1;}
 assert!(count==if n%29==0{0}else{DOT_COUNTS[n-1]});
}}

fn push_stub(dot:&mut crate::fast_pairing::EbyKDot,value:E,scalar:QM31)->Result<(),()>{unsafe{
 assert!(STAGE==9);assert!(MUL_CALLS==34);let n=CPUSH;assert!(n<174);
 let p=n/29;let l=n%29;assert!(CFINISH==p);assert!(CADD==0);
 assert!(CFIELD==if p==5{l+1}else{0});same_dot(dot,n);same_e(value,POWERS[l]);
 let sem=&*(SEM_PTR as *const Verified<Hash>);
 same_q(scalar,match p{0..=2=>sem.claims[p][l],3=>sem.extra[l],4=>sem.before_z1[l],_=>FIELDS[l].c0()});
 *dot=crate::fast_pairing::EbyKDot::proof_input(DOT_WORDS[n],DOT_COUNTS[n]);CPUSH=n+1;
 if n==STOP{Err(())}else{Ok(())}
}}

fn finish_stub(dot:crate::fast_pairing::EbyKDot)->E{unsafe{
 assert!(STAGE==9);assert!(MUL_CALLS==34);assert!(CADD==0);let p=CFINISH;assert!(p<6);
 assert!(CPUSH==29*(p+1));assert!(CFIELD==if p==5{29}else{0});
 let (words,count)=dot.proof_words();let mut i=0;
 while i<8{assert!(words[i]==DOT_WORDS[29*p+28][i]);i+=1;}
 assert!(count==DOT_COUNTS[29*p+28]);CFINISH=p+1;
 if p==5{STAGE=10;}DOT_RET[p]
}}

fn field_stub(bytes:&[u8],index:usize)->E{unsafe{
 assert!(STAGE==9);assert!(MUL_CALLS==34);assert!(CFINISH==5);assert!(CADD==0);
 assert!(bytes.as_ptr()==Y1_PTR);assert!(bytes.len()==928);assert!(index==CFIELD);
 assert!(index<29);assert!(CPUSH==145+index);CFIELD=index+1;FIELDS[index]
}}

fn add_stub(left:E,right:E)->E{unsafe{
 assert!(STAGE==10);let k=CADD;assert!(k<7);assert!(MUL_CALLS==35+k);
 assert!(CPUSH==174);assert!(CFINISH==6);assert!(CFIELD==29);
 same_e(left,if k==0{E::ZERO}else{ADDS[k-1]});same_e(right,MULTS[k]);CADD=k+1;
 if k==6{STAGE=12;}ADDS[k]
}}

fn any_q()->QM31{QM31{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}}}

fn any_row()->[QM31;29]{let mut row=[QM31::ZERO;29];let mut i=0;while i<29{row[i]=any_q();i+=1;}row}

fn any_challenges()->crate::r1_wire::Challenges{let mut zc=[QM31::ZERO;10];let mut i=0;while i<10{zc[i]=any_q();i+=1;}crate::r1_wire::Challenges{lambda:any_q(),chi:any_q(),theta:any_q(),zc,mu:any_q(),eta:any_q()}}

fn any_e()->E{let mut words=[0u32;8];let mut i=0;while i<8{let x=kani::any::<u32>()&0x7fff_ffff;words[i]=if x==0x7fff_ffff{0}else{x};i+=1;}match E::from_limbs(words){Some(e)=>e,None=>{assert!(false);E::ZERO}}}

fn any_es<const N:usize>()->[E;N]{let mut out=[E::ZERO;N];let mut i=0;while i<N{out[i]=any_e();i+=1;}out}
fn any_bytes()->[u8;928] {
 let mut out=[0u8;928];
 out[0..32].copy_from_slice(&kani::any::<[u8;32]>());
 out[32..64].copy_from_slice(&kani::any::<[u8;32]>());
 out[64..96].copy_from_slice(&kani::any::<[u8;32]>());
 out[96..128].copy_from_slice(&kani::any::<[u8;32]>());
 out[128..160].copy_from_slice(&kani::any::<[u8;32]>());
 out[160..192].copy_from_slice(&kani::any::<[u8;32]>());
 out[192..224].copy_from_slice(&kani::any::<[u8;32]>());
 out[224..256].copy_from_slice(&kani::any::<[u8;32]>());
 out[256..288].copy_from_slice(&kani::any::<[u8;32]>());
 out[288..320].copy_from_slice(&kani::any::<[u8;32]>());
 out[320..352].copy_from_slice(&kani::any::<[u8;32]>());
 out[352..384].copy_from_slice(&kani::any::<[u8;32]>());
 out[384..416].copy_from_slice(&kani::any::<[u8;32]>());
 out[416..448].copy_from_slice(&kani::any::<[u8;32]>());
 out[448..480].copy_from_slice(&kani::any::<[u8;32]>());
 out[480..512].copy_from_slice(&kani::any::<[u8;32]>());
 out[512..544].copy_from_slice(&kani::any::<[u8;32]>());
 out[544..576].copy_from_slice(&kani::any::<[u8;32]>());
 out[576..608].copy_from_slice(&kani::any::<[u8;32]>());
 out[608..640].copy_from_slice(&kani::any::<[u8;32]>());
 out[640..672].copy_from_slice(&kani::any::<[u8;32]>());
 out[672..704].copy_from_slice(&kani::any::<[u8;32]>());
 out[704..736].copy_from_slice(&kani::any::<[u8;32]>());
 out[736..768].copy_from_slice(&kani::any::<[u8;32]>());
 out[768..800].copy_from_slice(&kani::any::<[u8;32]>());
 out[800..832].copy_from_slice(&kani::any::<[u8;32]>());
 out[832..864].copy_from_slice(&kani::any::<[u8;32]>());
 out[864..896].copy_from_slice(&kani::any::<[u8;32]>());
 out[896..928].copy_from_slice(&kani::any::<[u8;32]>());
 out
}

fn run_profile<const POINT:usize>(negative:bool) {
 assert!(!core::mem::needs_drop::<crate::fast_pairing::EbyKDot>());
 assert!(!core::mem::needs_drop::<E>());
 assert!(!core::mem::needs_drop::<[[QM31;29];3]>());
 let mut alpha=[QM31::ZERO;10];let mut i=0;while i<10{alpha[i]=any_q();i+=1;}
 let sem=Verified{roots:kani::any(),challenges:any_challenges(),alpha,
  claims:Box::new([any_row(),any_row(),any_row()]),extra:any_row(),before_z1:any_row(),
  state_before_z0:kani::any(),z:[SecureCirclePoint{x:any_q(),y:any_q()},SecureCirclePoint{x:any_q(),y:any_q()}],
  transcript:crate::r1_wire::SemanticTranscript::proof_input(Hash,kani::any(),kani::any())};
 let y1=any_bytes();let inactive=any_e();let kappa=any_e();
 let mut powers=any_es::<29>();powers[0]=E::ONE;
 let mut kg=any_es::<7>();kg[0]=E::ONE;
 let dots=any_es::<6>();let fields=any_es::<29>();let mults=any_es::<7>();let adds=any_es::<7>();
 let stop=if POINT<6 {29*POINT+(kani::any::<u8>()%29)as usize}else{174};
 unsafe {
  STOP=stop;CPUSH=0;CFINISH=0;CFIELD=0;CADD=0;STAGE=8;MUL_CALLS=28;
  KG=kg;DOT_RET=dots;FIELDS=fields;MULTS=mults;ADDS=adds;
  DOT_WORDS=kani::any();DOT_COUNTS=kani::any();
  SCALARS[1]=kappa;POWERS=powers;INACTIVE=inactive;
  SEM_PTR=&sem as *const Verified<Hash> as *const ();Y1_PTR=y1.as_ptr();
 }
 let result=super::paired_reference::prepared_claim_owned(&sem,&y1,inactive,&powers,kappa);
 if stop<174 {
  assert!(result==Err(Error::Parse));
  assert!(unsafe{STAGE}==9);assert!(unsafe{MUL_CALLS}==34);
  assert!(unsafe{CPUSH}==stop+1);assert!(unsafe{CFINISH}==stop/29);
  assert!(unsafe{CFIELD}==if stop<145{0}else{stop-145+1});assert!(unsafe{CADD}==0);
  kani::cover!(stop<145,"semantic scalar first rejection");
  kani::cover!(stop>=145,"same y1 frame first rejection");
 } else {
  match result {Ok(value)=>same_e(value,adds[6]),Err(_)=>assert!(false)}
  assert!(!negative);
  assert!(unsafe{STAGE}==12);assert!(unsafe{MUL_CALLS}==41);
  assert!(unsafe{CPUSH}==174);assert!(unsafe{CFINISH}==6);
  assert!(unsafe{CFIELD}==29);assert!(unsafe{CADD}==7);
  kani::cover!(true,"same complete accepted profile");
 }
}

#[kani::proof]
#[kani::unwind(180)]
#[kani::stub(aspis_core::field::WideExact::mul,mul_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::push,push_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::finish,finish_stub)]
#[kani::stub(crate::weights::field,field_stub)]
#[kani::stub(aspis_core::field::WideExact::add,add_stub)]
fn borrowed_reference_matches_original_profile(){run_profile::<6>(false);}

#[kani::proof]
#[kani::unwind(180)]
#[kani::stub(aspis_core::field::WideExact::mul,mul_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::push,push_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::finish,finish_stub)]
#[kani::stub(crate::weights::field,field_stub)]
#[kani::stub(aspis_core::field::WideExact::add,add_stub)]
fn borrowed_reference_profile_negative(){run_profile::<6>(true);}


#[kani::proof]
#[kani::unwind(180)]
#[kani::stub(aspis_core::field::WideExact::mul,mul_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::push,push_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::finish,finish_stub)]
#[kani::stub(crate::weights::field,field_stub)]
#[kani::stub(aspis_core::field::WideExact::add,add_stub)]
fn borrowed_reference_profile_point_0(){run_profile::<0>(false);}

#[kani::proof]
#[kani::unwind(180)]
#[kani::stub(aspis_core::field::WideExact::mul,mul_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::push,push_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::finish,finish_stub)]
#[kani::stub(crate::weights::field,field_stub)]
#[kani::stub(aspis_core::field::WideExact::add,add_stub)]
fn borrowed_reference_profile_point_1(){run_profile::<1>(false);}

#[kani::proof]
#[kani::unwind(180)]
#[kani::stub(aspis_core::field::WideExact::mul,mul_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::push,push_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::finish,finish_stub)]
#[kani::stub(crate::weights::field,field_stub)]
#[kani::stub(aspis_core::field::WideExact::add,add_stub)]
fn borrowed_reference_profile_point_2(){run_profile::<2>(false);}

#[kani::proof]
#[kani::unwind(180)]
#[kani::stub(aspis_core::field::WideExact::mul,mul_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::push,push_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::finish,finish_stub)]
#[kani::stub(crate::weights::field,field_stub)]
#[kani::stub(aspis_core::field::WideExact::add,add_stub)]
fn borrowed_reference_profile_point_3(){run_profile::<3>(false);}

#[kani::proof]
#[kani::unwind(180)]
#[kani::stub(aspis_core::field::WideExact::mul,mul_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::push,push_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::finish,finish_stub)]
#[kani::stub(crate::weights::field,field_stub)]
#[kani::stub(aspis_core::field::WideExact::add,add_stub)]
fn borrowed_reference_profile_point_4(){run_profile::<4>(false);}

#[kani::proof]
#[kani::unwind(180)]
#[kani::stub(aspis_core::field::WideExact::mul,mul_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::push,push_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::finish,finish_stub)]
#[kani::stub(crate::weights::field,field_stub)]
#[kani::stub(aspis_core::field::WideExact::add,add_stub)]
fn borrowed_reference_profile_point_5(){run_profile::<5>(false);}

#[kani::proof]
#[kani::unwind(180)]
#[kani::stub(aspis_core::field::WideExact::mul,mul_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::push,push_stub)]
#[kani::stub(crate::fast_pairing::EbyKDot::finish,finish_stub)]
#[kani::stub(crate::weights::field,field_stub)]
#[kani::stub(aspis_core::field::WideExact::add,add_stub)]
fn borrowed_reference_profile_point_6(){run_profile::<6>(false);}
