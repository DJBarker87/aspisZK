from pathlib import Path
import subprocess,difflib
E=Path(__file__).resolve().parent
p='crates/aspis-core/src/r0/domain.rs';s=subprocess.check_output(['git','show','4bb3b3f5:'+p],text=True)
t=r'''
#[cfg(kani)]
mod NBS_indices {
 use super::*;
 #[kani::proof] #[kani::unwind(2)]
 fn fibre_total() {
  let u:usize=kani::any();
  match FibreIndex::new(u) {
   Ok(f)=>{assert!(u<262144);assert!(f.get()==u);},
   Err(e)=>{assert!(u>=262144);assert!(matches!(e,Error::IndexOutOfRange));}
  }
 }
 #[kani::proof] #[kani::unwind(2)]
 fn line_indices() {
  let u:usize=kani::any();kani::assume(u<262144);
  let x=u/4*4;let y=x+3;
  assert!(FibreIndex::new(x).unwrap().get()==x);
  assert!(FibreIndex::new(y).unwrap().get()==y);
  assert!(x<=u&&u<=y);assert!(x%4==0&&y%4==3);
  assert!((u&511)<512&&(u>>9)<512);
  assert!((u>>9)*512+(u&511)==u);
 }
}
'''
(E/'NBS_indices.patch').write_text(''.join(difflib.unified_diff(s.splitlines(True),(s+t).splitlines(True),fromfile='a/'+p,tofile='b/'+p)))
p='crates/aspis-r1-cost-probe/src/fast_domain.rs';s=subprocess.check_output(['git','show','4bb3b3f5:'+p],text=True)
t=r'''
#[cfg(kani)]
mod NBS_tables {
 use super::*;
 #[kani::proof] #[kani::unwind(4)]
 fn table_total() {
  let a:u32=kani::any();let b:u32=kani::any();let x=table_value((a,b));
  assert!(x.a.0==a);assert!(x.b.0==b);
 }
 #[kani::proof] #[kani::unwind(4)]
 fn table_canonical() {
  let i:usize=kani::any();kani::assume(i<512);
  assert!(TABLE_A[i].0<0x7fff_ffff);assert!(TABLE_A[i].1<0x7fff_ffff);
  assert!(TABLE_B[i].0<0x7fff_ffff);assert!(TABLE_B[i].1<0x7fff_ffff);
 }
}
'''
(E/'NBS_tables.patch').write_text(''.join(difflib.unified_diff(s.splitlines(True),(s+t).splitlines(True),fromfile='a/'+p,tofile='b/'+p)))
