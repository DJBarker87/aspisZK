#![allow(static_mut_refs)]
use super::*;
use alloc::boxed::Box;
use fast_pairing::EbyKDot;
#[derive(Clone,Copy)] struct Hash;
impl Digest32 for Hash {fn digest(&self,_:&[&[u8]])->[u8;32]{panic!("unused digest")}}
fn semantic(claims:[[[u32;4];29];3],extra:[[u32;4];29],before:[[u32;4];29])->r1_semantic::Verified<Hash> {
 use aspis_r1_cost_probe::r1_wire::{Challenges,SemanticTranscript};
 r1_semantic::Verified {
 roots:kani::any(),challenges:unsafe{core::mem::transmute(kani::any::<[u32;{core::mem::size_of::<Challenges>()/4}]>())},
 alpha:unsafe{core::mem::transmute(kani::any::<[[u32;4];10]>())},claims:Box::new(unsafe{core::mem::transmute(claims)}),extra:unsafe{core::mem::transmute(extra)},before_z1:unsafe{core::mem::transmute(before)},state_before_z0:kani::any(),
 z:unsafe{core::mem::transmute(kani::any::<[[u32;8];2]>())},transcript:SemanticTranscript::proof_input(Hash,kani::any(),kani::any()),
 }
}
static mut PUSH:usize=0; static mut FINISH:usize=0; static mut FIELD:usize=0;
static mut MUL:usize=0; static mut ADD:usize=0; static mut POWERS:usize=0;
static mut STOP:usize=174;
static mut STATES:[[u64;9];174]=[[0;9];174];
static mut FINISHES:[[u32;8];6]=[[0;8];6];
static mut FIELDS:[[u32;8];29]=[[0;8];29];
static mut MULTS:[[u32;8];7]=[[0;8];7];
static mut ADDS:[[u32;8];7]=[[0;8];7];
static mut KS:[[u32;8];7]=[[0;8];7];
static mut VALUES:[[u32;8];29]=[[0;8];29];
static mut CLAIMS:[[[u32;4];29];3]=[[[0;4];29];3];
static mut EXTRA:[[u32;4];29]=[[0;4];29];
static mut BEFORE:[[u32;4];29]=[[0;4];29];
static mut INACTIVE:[u32;8]=[0;8]; static mut KAPPA:[u32;8]=[0;8];
static mut Y1:*const u8=core::ptr::null();
fn eq4(a:[u32;4],b:[u32;4])->bool{(a[0]==b[0]) & (a[1]==b[1]) & (a[2]==b[2]) & (a[3]==b[3])}
fn eq8(a:[u32;8],b:[u32;8])->bool{(a[0]==b[0]) & (a[1]==b[1]) & (a[2]==b[2]) & (a[3]==b[3]) & (a[4]==b[4]) & (a[5]==b[5]) & (a[6]==b[6]) & (a[7]==b[7])}
fn eq9(a:[u64;9],b:[u64;9])->bool{(a[0]==b[0]) & (a[1]==b[1]) & (a[2]==b[2]) & (a[3]==b[3]) & (a[4]==b[4]) & (a[5]==b[5]) & (a[6]==b[6]) & (a[7]==b[7]) & (a[8]==b[8])}
fn words(e:E)->[u32;8]{unsafe{core::mem::transmute(e)}}
fn part(p:usize)->[u32;8]{unsafe{if p==0{INACTIVE}else{FINISHES[p-1]}}}
fn dot_words(d:&EbyKDot)->[u64;9]{unsafe{core::mem::transmute_copy(d)}}
fn expected_state(n:usize)->[u64;9]{unsafe{if n%29==0{[0;9]}else{STATES[n-1]}}}
fn push_leaf(dot:&mut EbyKDot,value:E,scalar:K)->Result<(),()> {unsafe {
 let n=PUSH;assert!(n<174);let p=n/29;let l=n%29;
 assert!(eq9(dot_words(dot),expected_state(n)));assert!(eq8(words(value),VALUES[l]));
 let expected=match p{0..=2=>CLAIMS[p][l],3=>EXTRA[l],4=>BEFORE[l],_=>[FIELDS[l][0],FIELDS[l][1],FIELDS[l][2],FIELDS[l][3]]};
 let actual:[u32;4]=core::mem::transmute(scalar);assert!(eq4(actual,expected));
 *dot=core::mem::transmute(STATES[n]);PUSH+=1;
 if n==STOP{Err(())}else{Ok(())}
}}
fn field_leaf(bytes:&[u8],index:usize)->E {unsafe {
 assert_eq!(bytes.as_ptr(),Y1);assert_eq!(bytes.len(),928);assert_eq!(FIELD,index);assert!(index<29);
 FIELD+=1;core::mem::transmute(FIELDS[index])
}}
fn finish_leaf(dot:EbyKDot)->E {unsafe {
 let p=FINISH;assert!(p<6);assert_eq!(PUSH,29*(p+1));assert!(eq9(dot_words(&dot),STATES[29*p+28]));
 FINISH+=1;core::mem::transmute(FINISHES[p])
}}
fn powers_leaf<const N:usize>(seed:E)->[E;N] {unsafe {
 assert_eq!(N,7);assert!(eq8(words(seed),KAPPA));assert_eq!(POWERS,0);POWERS+=1;
 let result:[E;7]=core::mem::transmute(KS);core::mem::transmute_copy(&result)
}}
fn mul_leaf(a:E,b:E)->E {unsafe {
 let i=MUL;assert!(i<7);assert!(eq8(words(a),KS[i]));assert!(eq8(words(b),part(i)));
 MUL+=1;core::mem::transmute(MULTS[i])
}}
fn add_leaf(a:E,b:E)->E {unsafe {
 let i=ADD;assert!(i<7);assert_eq!(MUL,i+1);
 assert!(eq8(words(a),if i==0{[0;8]}else{ADDS[i-1]}));assert!(eq8(words(b),MULTS[i]));
 ADD+=1;core::mem::transmute(ADDS[i])
}}
fn reset(){unsafe{PUSH=0;FINISH=0;FIELD=0;MUL=0;ADD=0;POWERS=0;}}
fn check_result(result:&Result<E,Error>){unsafe{
 assert_eq!(POWERS,1);
 if STOP<174{
  assert!(matches!(*result,Err(Error::Parse)));assert_eq!(PUSH,STOP+1);assert_eq!(FINISH,STOP/29);
  assert_eq!(FIELD,if STOP<145{0}else{STOP-145+1});assert_eq!(MUL,0);assert_eq!(ADD,0);
 }else{
  match result { Ok(value)=>assert!(eq8(words(*value),ADDS[6])),Err(_)=>assert!(false) };assert_eq!(PUSH,174);assert_eq!(FINISH,6);assert_eq!(FIELD,29);assert_eq!(MUL,7);assert_eq!(ADD,7);
 }
}}
#[kani::proof]
#[kani::stub(aspis_r1_cost_probe::weights::powers,powers_leaf)]
#[kani::stub(fast_pairing::EbyKDot::push,push_leaf)]
#[kani::stub(fast_pairing::EbyKDot::finish,finish_leaf)]
#[kani::stub(aspis_r1_cost_probe::weights::field,field_leaf)]
#[kani::stub(aspis_core::field::wide_exact::WideExact::mul,mul_leaf)]
#[kani::stub(aspis_core::field::wide_exact::WideExact::add,add_leaf)]
fn original_and_owned_word_exact_successful_children() {
 assert!(!core::mem::needs_drop::<EbyKDot>());
 let claims=kani::any();let extra=kani::any();let before=kani::any();
 let sem=semantic(claims,extra,before);let values:[[u32;8];29]=kani::any();let g:[E;29]=unsafe{core::mem::transmute(values)};
 let y1:[u8;928]=kani::any();let inactive:[u32;8]=kani::any();let kappa:[u32;8]=kani::any();
 unsafe{CLAIMS=claims;EXTRA=extra;BEFORE=before;VALUES=values;INACTIVE=inactive;KAPPA=kappa;Y1=y1.as_ptr();
 STOP=174;STATES=kani::any();FINISHES=kani::any();FIELDS=kani::any();MULTS=kani::any();ADDS=kani::any();KS=kani::any();}
 let inactive:E=unsafe{core::mem::transmute(inactive)};let kappa:E=unsafe{core::mem::transmute(kappa)};
 reset();let a=prepared_claim(&sem,&y1,inactive,&g,kappa);check_result(&a);
 reset();let b=prepared_claim_owned(&sem,&y1,inactive,&g,kappa);check_result(&b);assert!(match (a,b) {(Ok(x),Ok(y))=>eq8(words(x),words(y)),(Err(x),Err(y))=>x==y,_=>false});
}
