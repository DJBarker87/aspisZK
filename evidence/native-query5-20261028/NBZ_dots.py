from pathlib import Path
import difflib,json
E=Path(__file__).resolve().parent
s='''// Literal frozen four_dots_one stages, split at one source iteration/window.
extern crate alloc;
include!("KMX_stubs.rs");
use super::*;
const NBZ_P:u64=2147483647;const NBZ_D:u64=4611686009837453316;
fn NBZ_e()->E {let w:[u32;8]=kani::any();for x in w{kani::assume(x<2147483647);}E::from_limbs(w).unwrap()}
fn NBZ_g()->[E;29] {['''+','.join(['NBZ_e()']*29)+''']}
static mut NBZ_PHASE:usize=0;
static mut NBZ_CALLS:usize=0;
static mut NBZ_OLD:[u64;8]=[0;8];static mut NBZ_COEFF:[u32;8]=[0;8];static mut NBZ_SCALAR:[u32;8]=[0;8];static mut NBZ_OUT:[u64;8]=[0;8];
fn NBZ_add_expression(old:u64,x:u32,y:u32)->u64{old+u64::from(x)*u64::from(y)}
fn NBZ_add_spec(old:u64,x:u32,y:u32)->u64{
 assert!(u64::from(x)<NBZ_P&&u64::from(y)<NBZ_P);
 unsafe {assert!(NBZ_PHASE<4);assert!(old<(1u64<<34)+(NBZ_PHASE as u64)*NBZ_D);}
 let out:u64=kani::any();kani::assume(out as u128==old as u128+(x as u128)*(y as u128));
 unsafe {let i=NBZ_CALLS;assert!(i<8);NBZ_OLD[i]=old;NBZ_COEFF[i]=x;NBZ_SCALAR[i]=y;NBZ_OUT[i]=out;NBZ_CALLS+=1;}out
}
fn NBZ_base_iteration(q:&[u8;608],g:&[E;29],slot:usize,term:usize,sums:&mut[u64;8]) {
 let scalar=M31::from_le_bytes(q[slot*120+term*4..slot*120+term*4+4].try_into().unwrap()).unwrap();
 let coefficient=g[term].to_limbs();
'''
for k in range(8):s+=f' sums[{k}]=NBZ_add_expression(sums[{k}],coefficient[{k}],scalar.0);\n'
s+='''}
fn NBZ_base_case(negative:bool){
 let q:[u8;608]=kani::any();let g=NBZ_g();let slot:usize=kani::any();let term:usize=kani::any();let phase:usize=kani::any();let k:usize=kani::any();
 kani::assume(slot<4&&term<26&&phase<4&&k<8);
 let offset=slot*120+term*4;let scalar=u32::from_le_bytes([q[offset],q[offset+1],q[offset+2],q[offset+3]]);kani::assume(scalar<2147483647);
 let mut sums:[u64;8]=kani::any();for x in sums{kani::assume(x<(1u64<<34)+(phase as u64)*NBZ_D);}let old=sums[k];let coefficient=g[term].to_limbs()[k];
 unsafe{NBZ_PHASE=phase;}
 NBZ_base_iteration(&q,&g,slot,term,&mut sums);
 unsafe{assert_eq!(NBZ_CALLS,8);assert_eq!(NBZ_OLD[k],old);assert_eq!(NBZ_COEFF[k],coefficient);assert_eq!(NBZ_SCALAR[k],scalar);
 if negative{assert_ne!(sums[k],NBZ_OUT[k]);}else{assert_eq!(sums[k],NBZ_OUT[k]);}}
 kani::cover!(slot==3&&term==25&&k==7);kani::cover!(phase==0);kani::cover!(phase==3);
}
fn NBZ_fold_iteration(limbs:&mut[u64;8],sums:&[u64;8]) {
'''
for k in range(8):s+=f' limbs[{k}]+=(sums[{k}]&0x7fff_ffff)+(sums[{k}]>>31);\n'
s+='''}
fn NBZ_fold_case(negative:bool){
 let mut limbs:[u64;8]=kani::any();let sums:[u64;8]=kani::any();
 for x in limbs {kani::assume(x<6*(1u64<<34));}
 let k:usize=kani::any();kani::assume(k<8);let old=limbs[k];let input=sums[k];
 NBZ_fold_iteration(&mut limbs,&sums);
 let expected=old+(input%(1u64<<31))+(input/(1u64<<31));
 if negative{assert_ne!(limbs[k],expected);}else{assert_eq!(limbs[k],expected);}
 assert!(limbs[k]<7*(1u64<<34));kani::cover!(k==0);kani::cover!(k==7);
}
static mut NBZ_REDUCE_CALLS:usize=0;static mut NBZ_REDUCE_IN:[u64;8]=[0;8];static mut NBZ_REDUCE_OUT:[u32;8]=[0;8];
fn NBZ_reduce_spec(x:u64)->M31{let out:u32=kani::any();kani::assume(u64::from(out)==x%NBZ_P);unsafe{let i=NBZ_REDUCE_CALLS;assert!(i<8);NBZ_REDUCE_IN[i]=x;NBZ_REDUCE_OUT[i]=out;NBZ_REDUCE_CALLS+=1;}M31(out)}
fn NBZ_canonical_expression(limbs:[u64;8])->E {E::from_limbs([
'''+','.join(f'M31::reduce_u64(limbs[{k}]).0' for k in range(8))+''']).unwrap()}
fn NBZ_canonical_case(negative:bool){
 let limbs:[u64;8]=kani::any();let k:usize=kani::any();kani::assume(k<8);
 let out=NBZ_canonical_expression(limbs);
 unsafe{assert_eq!(NBZ_REDUCE_CALLS,8);assert_eq!(NBZ_REDUCE_IN[k],limbs[k]);
 if negative{assert_ne!(out.to_limbs()[k],NBZ_REDUCE_OUT[k]);}else{assert_eq!(out.to_limbs()[k],NBZ_REDUCE_OUT[k]);}}
 assert!(out.to_limbs()[k]<2147483647);kani::cover!(k==0);kani::cover!(k==7);
}
'''
attrs='''#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
#[kani::unwind(129)]
'''
rows=[]
for case,stub in [('base','#[kani::stub(NBZ_add_expression,NBZ_add_spec)]\n'),('fold',''),('canonical','#[kani::stub(aspis_core::field::M31::reduce_u64,NBZ_reduce_spec)]\n')]:
 for neg in [False,True]:
  name='NBZ_'+case+'_gate'+('_negative' if neg else '')
  s+=attrs+stub+'fn '+name+'(){NBZ_'+case+'_case('+str(neg).lower()+');}\n'
  rows.append(dict(harness='verifier::candidate::NBZ_dots::'+name,case=case,negative=neg))
Path('/tmp/NBZ_dots.rs').write_text(s)
(E/'NBZ_dots.patch').write_text(''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NBZ_dots.rs')))
(E/'NBZ_DOT_PLAN.json').write_text(json.dumps(rows,indent=2)+'\n')
