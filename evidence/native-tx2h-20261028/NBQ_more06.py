from pathlib import Path
import subprocess,difflib,tempfile
E=Path(__file__).resolve().parent;src='crates/aspis-r1-cost-probe/src/fast_pairing.rs';base=subprocess.check_output(['git','show','4bb3b3f5:'+src],text=True)
with tempfile.TemporaryDirectory() as d:
 q=Path(d)/src;q.parent.mkdir(parents=True);q.write_text(base)
 for p in ['NBQ_u06_initial.patch','NBQ_u06b.patch','NBQ_u06c.patch']:subprocess.run(['git','apply','-'],cwd=d,input=(E/p).read_text(),text=True,check=True)
 old=q.read_text()
s=old.replace('#[cfg(kani)] pub(super) fn NBQ_any_dot()', '#[cfg(kani)] pub(super) fn NBQ_sums(d:&Dot)->[u64;4]{d.sums}\n    #[cfg(kani)] pub(super) fn NBQ_any_dot()')
s+=r'''
#[cfg(kani)]
mod NBQ_more {
 use super::*;
 #[kani::proof] #[kani::unwind(12)]
 fn finish_all(){
  let a=canonical::NBQ_any_dot();let b=canonical::NBQ_any_dot();
  let av=canonical::NBQ_sums(&a);let bv=canonical::NBQ_sums(&b);
  let count:usize=kani::any();let out=EbyKDot{c0:a,c1:b,count}.finish().to_limbs();
  let j:usize=kani::any();kani::assume(j<8);
  assert!(u64::from(out[j])==(if j<4{av[j]}else{bv[j-4]})%u64::from(canonical::P));
 }
}
'''
(E/'NBQ_u06d.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/'+src,tofile='b/'+src)))
