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
static mut PUSH_INPUT:[u64;9]=[0;9];
static mut PUSH_VALUE:[u32;8]=[0;8];
static mut PUSH_SCALAR:[u32;4]=[0;4];
static mut PUSH_OUTPUT:[u64;9]=[0;9];
static mut ERROR:bool=false;
static mut PUSH_COUNT:usize=0;
static mut FIELD_INPUT:[u8;32]=[0;32];
static mut FIELD_OUTPUT:E=E::ZERO;
static mut FIELD_INDEX:usize=0;
static mut FIELD_COUNT:usize=0;
fn push_leaf(dot:&mut EbyKDot,value:E,scalar:K)->Result<(),()> {
 let state:[u64;9]=unsafe{core::mem::transmute_copy(&*dot)};
 let value:[u32;8]=unsafe{core::mem::transmute(value)};let scalar:[u32;4]=unsafe{core::mem::transmute(scalar)};
 unsafe{assert_eq!(PUSH_COUNT,0);PUSH_COUNT=1;
 if SECOND{assert_eq!(state,PUSH_INPUT);assert_eq!(value,PUSH_VALUE);assert_eq!(scalar,PUSH_SCALAR);}
 else{PUSH_INPUT=state;PUSH_VALUE=value;PUSH_SCALAR=scalar;}
 *dot=core::mem::transmute(PUSH_OUTPUT);if ERROR{Err(())}else{Ok(())}}
}
fn field_leaf(bytes:&[u8],index:usize)->E {
 assert_eq!(bytes.len(),928);assert!(index<29);
 let mut frame=[0;32];for j in 0..32{frame[j]=bytes[index*32+j];}
 unsafe{assert_eq!(FIELD_COUNT,0);FIELD_COUNT=1;
 if SECOND{assert_eq!(frame,FIELD_INPUT);assert_eq!(index,FIELD_INDEX);}else{FIELD_INPUT=frame;FIELD_INDEX=index;}
 FIELD_OUTPUT}
}
#[kani::proof]
#[kani::unwind(128)]
#[kani::stub(fast_pairing::EbyKDot::push,push_leaf)]
#[kani::stub(aspis_r1_cost_probe::weights::field,field_leaf)]
fn original_step_matches_owned() {
 let sem=semantic(kani::any(),kani::any(),kani::any());
 let point:usize=kani::any();let l:usize=kani::any();kani::assume(point<6&&l<29);
 let values:[[u32;8];29]=kani::any();let g:[E;29]=unsafe{core::mem::transmute(values)};
 let y1:[u8;928]=kani::any();let before:[u64;9]=kani::any();let after:[u64;9]=kani::any();
 let field:[u32;8]=kani::any();let error:bool=kani::any();
 let mut old:EbyKDot=unsafe{core::mem::transmute(before)};let new:EbyKDot=unsafe{core::mem::transmute(before)};
 unsafe{SECOND=false;PUSH_COUNT=0;FIELD_COUNT=0;ERROR=error;PUSH_OUTPUT=after;FIELD_OUTPUT=core::mem::transmute(field);}
 let a=original_step(&sem,&y1,&g,point,l,&mut old);
 let fields=unsafe{FIELD_COUNT};assert_eq!(unsafe{PUSH_COUNT},1);
 unsafe{SECOND=true;PUSH_COUNT=0;FIELD_COUNT=0;}
 let (b,new)=owned_step(&sem,y1,g,point,l,new);
 assert_eq!(a,b);assert_eq!(a,if error{Err(Error::Parse)}else{Ok(())});
 let old:[u64;9]=unsafe{core::mem::transmute(old)};let new:[u64;9]=unsafe{core::mem::transmute(new)};
 assert_eq!(old,new);assert_eq!(old,after);assert_eq!(unsafe{PUSH_COUNT},1);assert_eq!(unsafe{FIELD_COUNT},fields);
 assert_eq!(fields,if point==5{1}else{0});
 kani::cover!(point==5&&!error,"copied y1 frame accepts");kani::cover!(point==5&&error,"copied y1 frame rejects");kani::cover!(point<5&&error,"owned semantic row rejects");
}
