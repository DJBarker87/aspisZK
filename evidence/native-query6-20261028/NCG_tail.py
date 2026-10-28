from pathlib import Path
import difflib
E=Path(__file__).resolve().parent
s='''// Harness module inside the unchanged canonical implementation, in scratch only.
extern crate alloc;
include!("KMX_stubs.rs");
use super::{Q,Dot,P};
use super::super::{EbyKDot,E,CM31,QM31};
use aspis_core::field::M31;
static mut NCG_CALLS:usize=0;
static mut NCG_X:[[u32;4];2]=[[0;4];2];static mut NCG_Y:[[u32;4];2]=[[0;4];2];static mut NCG_O:[[u64;4];2]=[[0;4];2];
fn NCG_raw(x:Q,y:Q)->[u64;4]{for v in x.limbs(){assert!(v<P);}for v in y.limbs(){assert!(v<P);}let z:[u64;4]=kani::any();unsafe{let i=NCG_CALLS;assert!(i<2);NCG_X[i]=x.limbs();NCG_Y[i]=y.limbs();NCG_O[i]=z;NCG_CALLS+=1;}z}
fn NCG_q(x:[u32;4])->QM31{QM31{c0:CM31{a:M31(x[0]),b:M31(x[1])},c1:CM31{a:M31(x[2]),b:M31(x[3])}}}
fn NCG_tail_case(mode:usize,negative:bool){
 let words:[u32;8]=kani::any();for w in words{kani::assume(w<P);}let value=E::from_limbs(words).unwrap();
 let sc:[u32;4]=kani::any();let scalar=NCG_q(sc);let count:usize=kani::any();
 if mode==0{kani::assume(count<4096);for w in sc{kani::assume(w<P);}}
 if mode==1{kani::assume(count>=4096);}
 if mode==2{kani::assume(count<4096);kani::assume(sc[0]>=P||sc[1]>=P||sc[2]>=P||sc[3]>=P);}
 let old0:[u64;4]=kani::any();let old1:[u64;4]=kani::any();
 let mut state=EbyKDot{c0:Dot{sums:old0},c1:Dot{sums:old1},count};
 let result=state.push(value,scalar);
 let half:usize=kani::any();let k:usize=kani::any();kani::assume(half<2&&k<4);
 unsafe{
 if mode==0{
  assert_eq!(result,Ok(()));assert_eq!(NCG_CALLS,2);assert_eq!(NCG_X[half][k],words[half*4+k]);assert_eq!(NCG_Y[half][k],sc[k]);
  let prior=if half==0{old0[k]}else{old1[k]};let raw=NCG_O[half][k];let expected=prior.wrapping_add((raw&u64::from(P)).wrapping_add(raw>>31));
  let after=if half==0{state.c0.sums[k]}else{state.c1.sums[k]};
  if negative{assert_ne!(after,expected);}else{assert_eq!(after,expected);}assert_eq!(state.count,count+1);
 }else{
  assert_eq!(result,Err(()));assert_eq!(NCG_CALLS,0);assert_eq!(state.count,count);
  let after=if half==0{state.c0.sums[k]}else{state.c1.sums[k]};let prior=if half==0{old0[k]}else{old1[k]};
  if negative{assert_ne!(after,prior);}else{assert_eq!(after,prior);}
 }
 }
 kani::cover!(half==1&&k==3);kani::cover!(count==if mode==1{4096}else{0});
}
'''
attrs='''#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
#[kani::stub(super::Q::raw,NCG_raw)]
#[kani::unwind(129)]
'''
for mode in range(3):
 for neg in [False,True]:s+=attrs+f'fn NCG_tail_{mode}'+('_negative' if neg else '')+'(){NCG_tail_case('+str(mode)+','+str(neg).lower()+');}\n'
Path('/tmp/NCG_tail.rs').write_text(s)
(E/'NCG_tail.patch').write_text(''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NCG_tail.rs')))
