from pathlib import Path
import difflib,subprocess
E=Path(__file__).resolve().parent;p='crates/aspis-r1-cost-probe/src/fast_domain.rs'
s=subprocess.check_output(['git','show','4bb3b3f5:'+p],text=True)
# Cumulative NBS additions to the frozen source, excluding prior table patch
# in this extension's before-image.
old=s+''.join(line[1:] for line in (E/'NBS_tables.patch').read_text().splitlines(True) if line.startswith('+') and not line.startswith('+++'))
t=r'''
#[cfg(kani)]
mod NBS_route {
 use super::*;
 static mut EXPECT:usize=0;static mut CALLS:u8=0;static mut A:u32=0;static mut B:u32=0;
 fn cm_mul(x:CM31,y:CM31)->CM31 {
  unsafe {
   assert!(CALLS==0);CALLS=1;
   assert!(x.a.0==TABLE_A[EXPECT&511].0);assert!(x.b.0==TABLE_A[EXPECT&511].1);
   assert!(y.a.0==TABLE_B[EXPECT>>9].0);assert!(y.b.0==TABLE_B[EXPECT>>9].1);
  }
  assert!(x.a.0<0x7fff_ffff&&x.b.0<0x7fff_ffff&&y.a.0<0x7fff_ffff&&y.b.0<0x7fff_ffff);
  let p=2147483647u64;
  let a=u64::from(x.a.0);let b=u64::from(x.b.0);let c=u64::from(y.a.0);let d=u64::from(y.b.0);
  let ac=a.wrapping_mul(c)%p;let bd=b.wrapping_mul(d)%p;
  let cross=a.wrapping_add(b).wrapping_mul(c.wrapping_add(d))%p;
  let real=(ac+p-bd)%p;let imag=((cross+p-ac)%p+p-bd)%p;
  let ra:u32=kani::any();let rb:u32=kani::any();
  kani::assume(u64::from(ra)==real&&u64::from(rb)==imag);
  unsafe{A=ra;B=rb;}
  CM31::new(M31(ra),M31(rb))
 }
 #[kani::proof] #[kani::unwind(4)]
 #[kani::stub(CM31::mul,cm_mul)]
 fn fibre() {
  let u:usize=kani::any();kani::assume(u<262144);
  unsafe{EXPECT=u;CALLS=0;}
  let p=fibre_point(FibreIndex::new(u).unwrap());
  unsafe{assert!(CALLS==1);assert!(p.x.0==A);assert!(p.y.0==B);}
 }
}
'''
(E/'NBS_fast_route.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),(old+t).splitlines(True),fromfile='a/'+p,tofile='b/'+p)))
