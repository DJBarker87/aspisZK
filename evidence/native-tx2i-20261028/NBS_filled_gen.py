from pathlib import Path
import subprocess,difflib,tempfile
E=Path(__file__).resolve().parent;p='crates/aspis-core/src/r0/heap.rs'
s=subprocess.check_output(['git','show','4bb3b3f5:'+p],text=True)
t=r'''
#[cfg(kani)]
mod NBS_filled {
 use super::*;
 #[kani::proof] #[kani::unwind(4)]
 fn zst_positive() {
  let n:usize=kani::any();kani::assume(n>0);
  let v=filled(n,()).unwrap();assert!(v.len()==n);assert!(v.capacity()==usize::MAX);
  let i:usize=kani::any();kani::assume(i<n);assert!(v.get(i)==Some(&()));
 }
 #[kani::proof] #[kani::unwind(16)]
 fn one_qm31() {
  use crate::field::{M31,CM31,QM31};
  let a:u32=kani::any();let b:u32=kani::any();let c:u32=kani::any();let d:u32=kani::any();
  let x=QM31{c0:CM31{a:M31(a),b:M31(b)},c1:CM31{a:M31(c),b:M31(d)}};
  let v=filled(1,x).unwrap();assert!(v.len()==1);assert!(v.capacity()>=1);
  assert!(v[0].c0.a.0==a);assert!(v[0].c0.b.0==b);assert!(v[0].c1.a.0==c);assert!(v[0].c1.b.0==d);
 }
}
'''
# Existing inherited heap is unchanged; all NBQ additions are elsewhere.
(E/'NBS_filled.patch').write_text(''.join(difflib.unified_diff(s.splitlines(True),(s+t).splitlines(True),fromfile='a/'+p,tofile='b/'+p)))
