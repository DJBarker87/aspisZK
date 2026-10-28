from pathlib import Path
import subprocess,difflib,tempfile
E=Path(__file__).resolve().parent;paths=['crates/aspis-r1-cost-probe/src/fast_pairing.rs','crates/aspis-r1-cost-probe/src/fast_dots.rs','crates/aspis-r1-cost-probe/src/weights.rs']
with tempfile.TemporaryDirectory() as d:
 for p in paths:
  q=Path(d)/p;q.parent.mkdir(parents=True,exist_ok=True);q.write_text(subprocess.check_output(['git','show','4bb3b3f5:'+p],text=True))
 for patch in ['NBQ_u06_initial.patch','NBQ_u06b.patch','NBQ_u06c.patch','NBQ_u06d.patch','NBQ_u06e.patch','NBQ_u07.patch','NBQ_cells.patch']:
  subprocess.run(['git','apply','-'],input=(E/patch).read_text(),cwd=d,text=True,check=True)
 originals={p:(Path(d)/p).read_text() for p in paths}
p=paths[0];tail=r'''
#[cfg(kani)] pub(crate) fn NBQ_state(count:usize)->EbyKDot{EbyKDot{c0:canonical::NBQ_any_dot(),c1:canonical::NBQ_any_dot(),count}}
#[cfg(kani)] pub(crate) fn NBQ_count(s:&EbyKDot)->usize{s.count}
#[cfg(kani)] pub(crate) fn NBQ_advance(s:&mut EbyKDot){*s=NBQ_state(s.count+1);}
#[cfg(kani)] mod NBQ_reject_frame{
 use super::*;
 #[kani::proof] #[kani::unwind(64)]
 fn source(){let n:usize=kani::any();kani::assume(n>=4096);let mut s=NBQ_state(n);let a=canonical::NBQ_sums(&s.c0);let b=canonical::NBQ_sums(&s.c1);
 assert!(s.push(E::ZERO,QM31::ZERO).is_err());let j:usize=kani::any();kani::assume(j<4);assert!(canonical::NBQ_sums(&s.c0)[j]==a[j]);assert!(canonical::NBQ_sums(&s.c1)[j]==b[j]);assert!(s.count==n);}
}
'''
patch=''.join(difflib.unified_diff(originals[p].splitlines(True),(originals[p]+tail).splitlines(True),fromfile='a/'+p,tofile='b/'+p))
p=paths[1];tail=r'''
#[cfg(kani)] mod NBQ_tail {
 use super::*;
 static mut CALLS:usize=0; static mut COUNT:usize=0;
 static mut VPTR:*const WideExact=core::ptr::null();
 static mut DPTR:*mut EbyKDot=core::ptr::null_mut();
 fn push(s:&mut EbyKDot,v:WideExact,k:QM31)->Result<(),()>{unsafe{
  assert!(core::ptr::eq(s,DPTR));assert!(CALLS==0);assert!(crate::fast_pairing::NBQ_count(s)==COUNT);
  assert!(v==*VPTR);
  assert!(k.c0.a.0<0x7fff_ffff&&k.c0.b.0<0x7fff_ffff&&k.c1.a.0<0x7fff_ffff&&k.c1.b.0<0x7fff_ffff);
  assert!(COUNT<4096);crate::fast_pairing::NBQ_advance(s);CALLS+=1;Ok(())
 }}
 fn run<const POS:usize>(){
  let slot:usize=kani::any();kani::assume(slot<4);
  let mut q:[u8;608]=kani::any();
  let at=if POS==0{slot*120+104}else{480+slot*32+(POS-1)*16};
  for j in 0..4{let p=at+4*j;let w=u32::from_le_bytes([q[p],q[p+1],q[p+2],q[p+3]]);kani::assume(w<0x7fff_ffff);}
  let mut g=[WideExact::ZERO;29];let w:[u32;8]=kani::any();for v in w{kani::assume(v<0x7fff_ffff);}
  let ix=if POS==0{28}else{25+POS};g[ix]=WideExact::from_limbs(w).unwrap();
  let mut tail=crate::fast_pairing::NBQ_state(POS);
  unsafe{CALLS=0;COUNT=POS;VPTR=&g[ix];DPTR=&mut tail;}
  if POS==0{tail.push(g[28],QM31::from_le_bytes(&q[slot*120+104..slot*120+120]).unwrap()).unwrap();}
  else if POS==1{let offset0=480+slot*32+0*16;tail.push(g[0+26],QM31::from_le_bytes(&q[offset0..offset0+16]).unwrap()).unwrap();}
  else{let offset1=480+slot*32+1*16;tail.push(g[1+26],QM31::from_le_bytes(&q[offset1..offset1+16]).unwrap()).unwrap();}
  unsafe{assert!(CALLS==1);}assert!(crate::fast_pairing::NBQ_count(&tail)==POS+1);
 }
 #[kani::proof] #[kani::unwind(928)] #[kani::stub(EbyKDot::push,push)] fn first(){run::<0>();}
 #[kani::proof] #[kani::unwind(928)] #[kani::stub(EbyKDot::push,push)] fn second(){run::<1>();}
 #[kani::proof] #[kani::unwind(928)] #[kani::stub(EbyKDot::push,push)] fn third(){run::<2>();}
}
'''
patch+=''.join(difflib.unified_diff(originals[p].splitlines(True),(originals[p]+tail).splitlines(True),fromfile='a/'+p,tofile='b/'+p))
(E/'NBQ_tail.patch').write_text(patch)
