#![allow(static_mut_refs)]
use super::*;
use alloc::boxed::Box;
use aspis_core::field::{M31,CM31};
use fast_pairing::{EbyKDot,ProofQ};
#[derive(Clone,Copy)] struct Hash;
impl Digest32 for Hash {fn digest(&self,_:&[&[u8]])->[u8;32]{panic!("Digest32 must be unused in claim scope")}}
fn semantic(claims:[[[u32;4];29];3],extra:[[u32;4];29],before:[[u32;4];29])->r1_semantic::Verified<Hash> {
 use aspis_r1_cost_probe::r1_wire::{Challenges,SemanticTranscript};
 use aspis_core::circle::SecureCirclePoint;
 r1_semantic::Verified {
 roots:kani::any(),challenges:unsafe{core::mem::transmute(kani::any::<[u32;{core::mem::size_of::<Challenges>()/4}]>())},
 alpha:unsafe{core::mem::transmute(kani::any::<[[u32;4];10]>())},claims:Box::new(unsafe{core::mem::transmute(claims)}),extra:unsafe{core::mem::transmute(extra)},before_z1:unsafe{core::mem::transmute(before)},state_before_z0:kani::any(),
 z:unsafe{core::mem::transmute(kani::any::<[[u32;8];2]>())},transcript:SemanticTranscript::proof_input(Hash,kani::any(),kani::any()),
 }
}

static mut SECOND:bool=false;
static mut COUNT:usize=0;
static mut STOP:usize=29;
static mut INPUTS:[[u64;21];29]=[[0;21];29];
static mut OUTPUTS:[[u64;9];29]=[[0;9];29];
static mut FIELDS:[E;29]=[E::ZERO;29];
static mut FIELD_COUNT:usize=0;
static mut Y1:*const u8=core::ptr::null();
static mut FINISH_COUNT:usize=0;
static mut FINISH_INPUT:[u64;9]=[0;9];
static mut FINISH_OUTPUT:E=E::ZERO;
fn push_leaf(dot:&mut EbyKDot,value:E,scalar:K)->Result<(),()> {
 let s:[u64;9]=unsafe{core::mem::transmute_copy(&*dot)};
 let v:[u32;8]=unsafe{core::mem::transmute(value)};let q:[u32;4]=unsafe{core::mem::transmute(scalar)};
 let input=[s[0],s[1],s[2],s[3],s[4],s[5],s[6],s[7],s[8],u64::from(v[0]),u64::from(v[1]),u64::from(v[2]),u64::from(v[3]),u64::from(v[4]),u64::from(v[5]),u64::from(v[6]),u64::from(v[7]),u64::from(q[0]),u64::from(q[1]),u64::from(q[2]),u64::from(q[3])];
 unsafe{let i=COUNT;assert!(i<29);if SECOND{assert_eq!(input,INPUTS[i]);}else{INPUTS[i]=input;}
 COUNT=i+1;*dot=core::mem::transmute(OUTPUTS[i]);if i==STOP{Err(())}else{Ok(())}}
}
fn field_leaf(bytes:&[u8],index:usize)->E {
 unsafe{assert_eq!(bytes.as_ptr(),Y1);assert_eq!(bytes.len(),928);assert_eq!(index,FIELD_COUNT);assert!(index<29);FIELD_COUNT+=1;FIELDS[index]}
}
fn finish_leaf(dot:EbyKDot)->E {
 let input:[u64;9]=unsafe{core::mem::transmute(dot)};
 unsafe{assert_eq!(FINISH_COUNT,0);if SECOND{assert_eq!(input,FINISH_INPUT);}else{FINISH_INPUT=input;}FINISH_COUNT=1;FINISH_OUTPUT}
}
#[kani::proof]
#[kani::unwind(128)]
#[kani::stub(fast_pairing::EbyKDot::push,push_leaf)]
#[kani::stub(fast_pairing::EbyKDot::finish,finish_leaf)]
#[kani::stub(aspis_r1_cost_probe::weights::field,field_leaf)]
fn original_point_replays_fission() {
 assert!(!core::mem::needs_drop::<EbyKDot>());
 let sem=semantic(kani::any(),kani::any(),kani::any());let point:usize=kani::any();kani::assume(point<6);
 let stop:usize=kani::any();kani::assume(stop<=29);
 let coeffs:[[u32;8];29]=kani::any();let g:[E;29]=unsafe{core::mem::transmute(coeffs)};
 let parts:[[u32;8];7]=kani::any();let initial:[E;7]=unsafe{core::mem::transmute(parts)};let mut old=initial;let mut new=initial;
 let y1:[u8;928]=kani::any();let fields:[[u32;8];29]=kani::any();let finish:[u32;8]=kani::any();let outputs:[[u64;9];29]=kani::any();
 unsafe{SECOND=false;COUNT=0;STOP=stop;OUTPUTS=outputs;FIELDS=core::mem::transmute(fields);FIELD_COUNT=0;FINISH_COUNT=0;FINISH_OUTPUT=core::mem::transmute(finish);Y1=y1.as_ptr();}
 let a=original_point_step(&sem,&y1,&g,point,&mut old);
 let count=unsafe{COUNT};let fields=unsafe{FIELD_COUNT};let finished=unsafe{FINISH_COUNT};
 unsafe{SECOND=true;COUNT=0;FIELD_COUNT=0;FINISH_COUNT=0;}
 let b=reference_point_step(&sem,&y1,&g,point,&mut new);
 assert_eq!(a,b);assert_eq!(old,new);
 assert_eq!(unsafe{COUNT},count);assert_eq!(unsafe{FIELD_COUNT},fields);assert_eq!(unsafe{FINISH_COUNT},finished);
 assert_eq!(count,if stop==29{29}else{stop+1});assert_eq!(finished,if stop==29{1}else{0});
 assert_eq!(a,if stop==29{Ok(())}else{Err(Error::Parse)});
 if stop<29{assert_eq!(old,initial);}
 kani::cover!(stop==29&&point==5,"complete y1 point");kani::cover!(stop==28&&point==5,"last y1 push rejects");kani::cover!(stop==0,"first push rejects");
}
