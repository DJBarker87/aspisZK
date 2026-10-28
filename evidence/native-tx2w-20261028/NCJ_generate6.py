from NCJ_host import *
import difflib
admit('NCJ_INSTALL008')
source=r'''
use super::{Q,Dot,P};use super::super::{EbyKDot,E,CM31,QM31};use aspis_core::field::M31;
static mut NCJ_RN:usize=0;static mut NCJ_X:[[u32;4];2]=[[0;4];2];static mut NCJ_Y:[[u32;4];2]=[[0;4];2];static mut NCJ_R:[[u64;4];2]=[[0;4];2];
static mut NCJ_FN:usize=0;static mut NCJ_FI:usize=0;static mut NCJ_FL:usize=0;static mut NCJ_FB:u8=0;static mut NCJ_SEEK:usize=0;static mut NCJ_FV:E=E::ZERO;
fn word()->u32{let x:u32=kani::any();kani::assume(x<P);x}
fn ce()->E{E::from_limbs([word(),word(),word(),word(),word(),word(),word(),word()]).unwrap()}
fn cq()->QM31{QM31{c0:CM31{a:M31(word()),b:M31(word())},c1:CM31{a:M31(word()),b:M31(word())}}}
fn NCJ_raw(x:Q,y:Q)->[u64;4]{for v in x.limbs(){assert!(v<P);}for v in y.limbs(){assert!(v<P);}let r:[u64;4]=kani::any();unsafe{let k=NCJ_RN;assert!(k<2);NCJ_X[k]=x.limbs();NCJ_Y[k]=y.limbs();NCJ_R[k]=r;NCJ_RN=k+1;}r}
fn NCJ_field(b:&[u8],i:usize)->E{let v=ce();assert!(i<64);assert_eq!(b.len(),2048);unsafe{NCJ_FN+=1;NCJ_FI=i;NCJ_FL=b.len();NCJ_FB=b[NCJ_SEEK];NCJ_FV=v;}v}
fn NCJ_case(mode:u8,bad:bool){
 let bound=if mode==0{16}else if mode==1{4}else{64};let j:usize=kani::any();kani::assume(j<bound);
 let s:usize=kani::any();kani::assume(s<4);let count:usize=kani::any();kani::assume(count<if mode==0{16}else if mode==1{4}else{64});
 let scalar=cq();let value=ce();let mut common=[QM31::ZERO;64];common[j]=scalar;let mut partials=[E::ZERO;4];if mode==1{partials[j]=value;}
 let old0:[u64;4]=kani::any();let old1:[u64;4]=kani::any();let mut dot=EbyKDot{c0:Dot{sums:old0},c1:Dot{sums:old1},count};
 let mut bytes=[0u8;2048];let seek:usize=kani::any();kani::assume(seek<2048);let byte:u8=kani::any();kani::assume(seek%4!=3||byte<128);bytes[seek]=byte;
 unsafe{NCJ_RN=0;NCJ_FN=0;NCJ_SEEK=seek;}
 let result:Result<(),crate::verifier::Error> = if mode==0{
  match dot.push(crate::weights::field(&bytes,16*s+j),common[j]){Ok(())=>Ok(()),Err(_)=>Err(crate::verifier::Error::Parse)}
 }else if mode==1{
  match dot.push(partials[j],common[j]){Ok(())=>Ok(()),Err(_)=>Err(crate::verifier::Error::Parse)}
 }else if mode==2{
  match dot.push(crate::weights::field(&bytes,j),common[j]){Ok(())=>Ok(()),Err(_)=>Err(crate::verifier::Error::Parse)}
 }else{
  dot.push(crate::weights::field(&bytes,j),common[j]).map_err(|_|crate::verifier::Error::Parse)
 };
 assert_eq!(result,Ok(()));assert_eq!(dot.count,count+1);
 let half:usize=kani::any();let k:usize=kani::any();kani::assume(half<2&&k<4);
 unsafe{
  assert_eq!(NCJ_RN,2);let input=if mode==1{value}else{NCJ_FV};let limbs=input.to_limbs();
  assert_eq!(NCJ_X[half][k],limbs[4*half+k]);let q=[scalar.c0.a.0,scalar.c0.b.0,scalar.c1.a.0,scalar.c1.b.0];assert_eq!(NCJ_Y[half][k],q[k]);
  let raw=NCJ_R[half][k];let prior=if half==0{old0[k]}else{old1[k]};let expected=prior.wrapping_add((raw&u64::from(P)).wrapping_add(raw>>31));let after=if half==0{dot.c0.sums[k]}else{dot.c1.sums[k]};if bad{assert_ne!(after,expected);}else{assert_eq!(after,expected);}
  if mode==1{assert_eq!(NCJ_FN,0);}else{assert_eq!(NCJ_FN,1);assert_eq!(NCJ_FI,if mode==0{16*s+j}else{j});assert_eq!(NCJ_FL,2048);assert_eq!(NCJ_FB,byte);}
 }
}
'''
attrs='''#[kani::proof] #[kani::unwind(66)]
#[kani::stub(super::Q::raw,NCJ_raw)]
#[kani::stub(crate::weights::field,NCJ_field)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
'''
for mode,name in enumerate(['partial','high','bytes','final']):
 for bad in [False,True]:source+=attrs+f'fn NCJ_{name}_{"negative" if bad else "positive"}(){{NCJ_case({mode},{str(bad).lower()});}}\n'
r=py(f"from pathlib import Path;print((Path({B!r})/'NCJ_src/crates/aspis-r1-cost-probe/src/fast_pairing.rs').read_text(),end='')");assert r.returncode==0
before=r.stdout;needle='    pub struct Dot { sums:[u64;4] }';assert before.count(needle)==1
after=before.replace(needle,needle+'\n    #[cfg(kani)] #[path="../../NCJ_dot.rs"] mod NCJ_dot;',1)
p='crates/aspis-r1-cost-probe/src/fast_pairing.rs';q='crates/aspis-r1-cost-probe/src/NCJ_dot.rs'
patch=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+p,tofile='b/'+p))+''.join(difflib.unified_diff([],source.splitlines(True),fromfile='/dev/null',tofile='b/'+q));(E/'NCJ_stage6.patch').write_text(patch)
r=py(f'''from pathlib import Path
s=Path({(B+'/NCJ_src')!r});p=s/{p!r};assert p.read_text()=={before!r};p.write_text({after!r});(s/{q!r}).write_text({source!r});(s/'crates/aspis-r1-cost-probe/src/fast_pairing').mkdir(exist_ok=True);(s/'crates/aspis-r1-cost-probe/src/fast_pairing/canonical').mkdir(exist_ok=True)
''');assert r.returncode==0,r.stderr
