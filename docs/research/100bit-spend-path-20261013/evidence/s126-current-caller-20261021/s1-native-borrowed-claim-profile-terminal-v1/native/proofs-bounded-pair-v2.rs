#![allow(static_mut_refs)]
use super::Error;
use alloc::boxed::Box;
use aspis_core::{Digest32,field::{WideExact as E,QM31,CM31,M31},circle::SecureCirclePoint};
use crate::{fast_pairing::EbyKDot,r1_semantic::Verified};

#[derive(Clone,Copy)] struct Hash;
impl Digest32 for Hash {
    fn digest(&self,_:&[&[u8]])->[u8;32] { panic!("claim must not read Digest32") }
}

static mut SECOND:bool=false;
static mut STOP:usize=174;
static mut PUSH:usize=0;
static mut FINISH:usize=0;
static mut FIELD:usize=0;
static mut MUL:usize=0;
static mut ADD:usize=0;
static mut TOTAL:[usize;5]=[0;5];
static mut PUSH_STATE:[[u64;8];174]=[[0;8];174];
static mut PUSH_COUNT:[usize;174]=[0;174];
static mut PUSH_VALUE:[E;174]=[E::ZERO;174];
static mut PUSH_SCALAR:[QM31;174]=[QM31::ZERO;174];
static mut PUSH_REPLY:[[u64;8];174]=[[0;8];174];
static mut PUSH_REPLY_COUNT:[usize;174]=[0;174];
static mut FINISH_STATE:[[u64;8];6]=[[0;8];6];
static mut FINISH_COUNT:[usize;6]=[0;6];
static mut FINISH_REPLY:[E;6]=[E::ZERO;6];
static mut FIELD_POINTER:[*const u8;29]=[core::ptr::null();29];
static mut FIELD_LENGTH:[usize;29]=[0;29];
static mut FIELD_INDEX:[usize;29]=[0;29];
static mut FIELD_REPLY:[E;29]=[E::ZERO;29];
// Six kappa-power multiplications plus seven weighted terms. Inputs and
// outputs are full native carriers, never a hash or reduced projection.
static mut MUL_INPUT:[(E,E);13]=[(E::ZERO,E::ZERO);13];
static mut MUL_REPLY:[E;13]=[E::ZERO;13];
static mut ADD_INPUT:[(E,E);7]=[(E::ZERO,E::ZERO);7];
static mut ADD_REPLY:[E;7]=[E::ZERO;7];

fn any_q()->QM31 {QM31{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}}}
fn any_row()->[QM31;29] {let mut row=[QM31::ZERO;29];for value in &mut row {*value=any_q();}row}
fn any_e()->E {
    let mut words=[0u32;8];
    for word in &mut words {
        let raw=kani::any::<u32>()&0x7fff_ffff;
        *word=if raw==0x7fff_ffff {0}else{raw};
    }
    E::from_limbs(words).unwrap()
}
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
fn same_e(a:E,b:E) {assert!(a.to_limbs()==b.to_limbs());}
fn same_q(a:QM31,b:QM31) {
    assert!(a.c0.a.0==b.c0.a.0);assert!(a.c0.b.0==b.c0.b.0);
    assert!(a.c1.a.0==b.c1.a.0);assert!(a.c1.b.0==b.c1.b.0);
}

fn push(dot:&mut EbyKDot,value:E,scalar:QM31)->Result<(),()> {unsafe {
    let n=PUSH;assert!(n<174);let (words,count)=dot.proof_words();
    if SECOND {
        assert!(words==PUSH_STATE[n]);assert!(count==PUSH_COUNT[n]);
        same_e(value,PUSH_VALUE[n]);same_q(scalar,PUSH_SCALAR[n]);
    } else {
        PUSH_STATE[n]=words;PUSH_COUNT[n]=count;PUSH_VALUE[n]=value;PUSH_SCALAR[n]=scalar;
        PUSH_REPLY[n]=kani::any();PUSH_REPLY_COUNT[n]=kani::any();
    }
    *dot=EbyKDot::proof_input(PUSH_REPLY[n],PUSH_REPLY_COUNT[n]);PUSH=n+1;
    if n==STOP {Err(())}else{Ok(())}
}}
fn finish(dot:EbyKDot)->E {unsafe {
    let n=FINISH;assert!(n<6);let (words,count)=dot.proof_words();
    if SECOND {assert!(words==FINISH_STATE[n]);assert!(count==FINISH_COUNT[n]);}
    else {FINISH_STATE[n]=words;FINISH_COUNT[n]=count;FINISH_REPLY[n]=any_e();}
    FINISH=n+1;FINISH_REPLY[n]
}}
fn field(bytes:&[u8],index:usize)->E {unsafe {
    let n=FIELD;assert!(n<29);
    if SECOND {
        assert!(bytes.as_ptr()==FIELD_POINTER[n]);assert!(bytes.len()==FIELD_LENGTH[n]);
        assert!(index==FIELD_INDEX[n]);
    } else {
        FIELD_POINTER[n]=bytes.as_ptr();FIELD_LENGTH[n]=bytes.len();FIELD_INDEX[n]=index;
        FIELD_REPLY[n]=any_e();
    }
    FIELD=n+1;FIELD_REPLY[n]
}}
fn multiply(left:E,right:E)->E {unsafe {
    let n=MUL;assert!(n<13);
    if SECOND {same_e(left,MUL_INPUT[n].0);same_e(right,MUL_INPUT[n].1);}
    else {MUL_INPUT[n]=(left,right);MUL_REPLY[n]=any_e();}
    MUL=n+1;MUL_REPLY[n]
}}
fn add(left:E,right:E)->E {unsafe {
    let n=ADD;assert!(n<7);
    if SECOND {same_e(left,ADD_INPUT[n].0);same_e(right,ADD_INPUT[n].1);}
    else {ADD_INPUT[n]=(left,right);ADD_REPLY[n]=any_e();}
    ADD=n+1;ADD_REPLY[n]
}}

fn run(negative:bool) {
    assert!(!core::mem::needs_drop::<EbyKDot>());
    assert!(!core::mem::needs_drop::<E>());
    assert!(!core::mem::needs_drop::<[[QM31;29];3]>());
    let mut zc=[QM31::ZERO;10];for value in &mut zc {*value=any_q();}
    let challenges=crate::r1_wire::Challenges{lambda:any_q(),chi:any_q(),theta:any_q(),zc,mu:any_q(),eta:any_q()};
    let mut alpha=[QM31::ZERO;10];for value in &mut alpha {*value=any_q();}
    let sem=Verified{roots:kani::any(),challenges,alpha,
        claims:Box::new([any_row(),any_row(),any_row()]),extra:any_row(),before_z1:any_row(),
        state_before_z0:kani::any(),z:[SecureCirclePoint{x:any_q(),y:any_q()},SecureCirclePoint{x:any_q(),y:any_q()}],
        transcript:crate::r1_wire::SemanticTranscript::proof_input(Hash,kani::any(),kani::any())};
    let bytes=any_bytes();
    let mut g=[E::ZERO;29];for value in &mut g {*value=any_e();}
    let inactive=any_e();let kappa=any_e();
    let stop:usize=kani::any();kani::assume(stop<=174);
    unsafe {SECOND=false;STOP=stop;PUSH=0;FINISH=0;FIELD=0;MUL=0;ADD=0;}
    let original=super::prepared_claim(&sem,&bytes,inactive,&g,kappa);
    unsafe {TOTAL=[PUSH,FINISH,FIELD,MUL,ADD];SECOND=true;PUSH=0;FINISH=0;FIELD=0;MUL=0;ADD=0;}
    let reference=super::paired_reference::prepared_claim_owned(&sem,&bytes,inactive,&g,kappa);
    unsafe {assert!(TOTAL==[PUSH,FINISH,FIELD,MUL,ADD]);}
    match (original,reference) {
        (Ok(a),Ok(b))=> {same_e(a,b);assert!(!negative);kani::cover!(true,"same complete accepted claim");},
        (Err(a),Err(b))=> {assert!(a==b);assert!(a==Error::Parse);kani::cover!(true,"same first rejection");},
        _=>assert!(false,"whole original/reference result classification differs"),
    }
}

#[kani::proof]
#[kani::unwind(180)]
#[kani::stub(crate::fast_pairing::EbyKDot::push,push)]
#[kani::stub(crate::fast_pairing::EbyKDot::finish,finish)]
#[kani::stub(crate::weights::field,field)]
#[kani::stub(aspis_core::field::WideExact::mul,multiply)]
#[kani::stub(aspis_core::field::WideExact::add,add)]
fn complete_original_matches_borrowed_reference() {run(false);}

#[kani::proof]
#[kani::unwind(180)]
#[kani::stub(crate::fast_pairing::EbyKDot::push,push)]
#[kani::stub(crate::fast_pairing::EbyKDot::finish,finish)]
#[kani::stub(crate::weights::field,field)]
#[kani::stub(aspis_core::field::WideExact::mul,multiply)]
#[kani::stub(aspis_core::field::WideExact::add,add)]
fn accepted_result_negative_control() {run(true);}
