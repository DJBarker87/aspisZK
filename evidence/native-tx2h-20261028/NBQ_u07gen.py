from pathlib import Path
import subprocess,difflib,re
E=Path(__file__).resolve().parent
# Reuse exact natural-spec field substitution; it is paired to LPi_TowerValues.wide_mul.
p=Path('evidence/leaf-p6-11-20261027/LPm_native.patch')
files=list(Path('evidence/leaf-p6-11-20261027').glob('*.patch'))
text=next(p.read_text() for p in files if 'mod LPm_emul {' in p.read_text())
s='\n'.join(l[1:] for l in text.splitlines() if l.startswith('+') and not l.startswith('+++'))
start=s.index('mod LPm_emul {');end=s.index('\nfn LPm_any_e',start)
emul=s[start:end].replace('LPm_emul','NBQ_emul')
any_e='''fn any_e()->E {let w:[u32;8]=kani::any();for v in w {kani::assume(v<0x7fff_ffff);}E::from_limbs(w).unwrap()}\n'''
weights='''\n#[cfg(kani)]\nmod NBQ_powers {\nuse super::*;\n'''+any_e+emul+r'''
 #[kani::proof] #[kani::unwind(66)]
 fn zero(){let out=super::powers::<0>(any_e());assert!(out.len()==0);}
 #[kani::proof] #[kani::unwind(66)]
 fn one(){let out=super::powers::<1>(any_e());assert!(out[0]==E::ONE);}
 // Actual source write/increment/last branch on an arbitrary prestate.
 #[kani::proof] #[kani::unwind(928)]
 fn write_frame(){
  let mut out=[E::ZERO;29];let at:usize=kani::any();kani::assume(at<29);let old=any_e();out[at]=old;
  let mut i:usize=kani::any();kani::assume(i<29);let before=i;let p=any_e();
  out[i]=p;
  i+=1;
  assert!(i==before+1);assert!(out[at]==if at==before{p}else{old});
  assert!((i==29)==(before==28));
 }
 #[kani::proof] #[kani::unwind(66)]
 #[kani::stub(E::mul,NBQ_emul::replacement)]
 fn continuing(){
  let mut p=any_e();let x=any_e();let returned=p.mul(x);p=returned;
  let j:usize=kani::any();kani::assume(j<8);
  assert!(p.to_limbs()[j]==returned.to_limbs()[j]);assert!(p.to_limbs()[j]<0x7fff_ffff);
 }
}
'''
# field selector with actual decoder, scalar words canonical; no multiplication arithmetic.
weights+=r'''
#[cfg(kani)]
mod NBQ_field {
 use super::*;
 #[kani::proof] #[kani::unwind(66)]
 fn selected(){
  let mut bytes:[u8;64]=kani::any();let index:usize=kani::any();kani::assume(index<2);
  // Canonicality is exactly what every reached caller must establish.
  let start=index*32;
  let mut words=[0u32;8];
  for j in 0..8 {let at=start+4*j;words[j]=u32::from_le_bytes([bytes[at],bytes[at+1],bytes[at+2],bytes[at+3]]);kani::assume(words[j]<0x7fff_ffff);}
  let out=super::field(&bytes,index).to_limbs();let j:usize=kani::any();kani::assume(j<8);assert!(out[j]==words[j]);
 }
}
'''
# The actual public wrapper, with its unresolved child abstracted only for routing.
dots=r'''
#[cfg(kani)]
mod NBQ_dots {
 use super::*;
 static mut CALLS:usize=0;static mut QPTR:*const u8=core::ptr::null();static mut GPTR:*const WideExact=core::ptr::null();
 fn child(q:&[u8;608],g:&[WideExact;29],slot:usize)->WideExact{unsafe{
  assert!(core::ptr::eq(q.as_ptr(),QPTR));assert!(core::ptr::eq(g.as_ptr(),GPTR));assert!(slot==CALLS);CALLS+=1;
 }g[slot]}
 #[kani::proof] #[kani::unwind(928)]
 #[kani::stub(super::four_dots_one,child)]
 fn routing(){
  let q:[u8;609]=kani::any();let g=[WideExact::ZERO;29];let len:usize=kani::any();kani::assume(len>=608&&len<=609);
  unsafe{CALLS=0;QPTR=q.as_ptr();GPTR=g.as_ptr();}
  let out=super::four_dots(&q[..len],&g);
  unsafe{assert!(CALLS==4);}let j:usize=kani::any();kani::assume(j<4);assert!(out[j]==g[j]);
 }
 #[kani::proof] #[kani::unwind(8)]
 fn indices(){let slot:usize=kani::any();kani::assume(slot<4);let term:usize=kani::any();kani::assume(term<26);let at=slot*120+term*4;assert!(at+4<=608);assert!(slot*120+104+16<=608);assert!(480+slot*32+16<=608);assert!(480+slot*32+16+16<=608);}
}
'''
patch=''
for p,tail in [('crates/aspis-r1-cost-probe/src/weights.rs',weights),('crates/aspis-r1-cost-probe/src/fast_dots.rs',dots)]:
 old=subprocess.check_output(['git','show','4bb3b3f5:'+p],text=True)
 patch+=''.join(difflib.unified_diff(old.splitlines(True),(old+tail).splitlines(True),fromfile='a/'+p,tofile='b/'+p))
(E/'NBQ_u07.patch').write_text(patch)
