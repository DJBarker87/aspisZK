from pathlib import Path
import subprocess,difflib
E=Path(__file__).resolve().parent;p='crates/aspis-r1-cost-probe/src/fast_domain.rs'
s=subprocess.check_output(['git','show','4bb3b3f5:'+p],text=True)
for name in ['NBS_tables.patch','NBS_fast_route.patch']:
 s+=''.join(l[1:] for l in (E/name).read_text().splitlines(True) if l.startswith('+') and not l.startswith('+++'))
# Extend the SAME private route module, no existing harness edited.
needle='\n}\n';at=s.rfind(needle)
t=r'''
 static mut SQUARE:u32=0;static mut MCALLS:u8=0;
 fn base_mul(x:M31,y:M31)->M31 {
  unsafe{assert!(MCALLS==0);MCALLS=1;assert!(x.0==A);assert!(y.0==A);}
  assert!(x.0<2147483647&&y.0<2147483647);
  let reply:u32=kani::any();
  kani::assume(u64::from(reply)==u64::from(x.0).wrapping_mul(u64::from(y.0))%2147483647);
  unsafe{SQUARE=reply;}
  M31(reply)
 }
 #[kani::proof] #[kani::unwind(4)]
 #[kani::stub(CM31::mul,cm_mul)] #[kani::stub(M31::mul,base_mul)]
 fn line() {
  let u:usize=kani::any();kani::assume(u<262144);
  unsafe{EXPECT=u;CALLS=0;MCALLS=0;}
  let result=line_node(FibreIndex::new(u).unwrap());
  unsafe{
   assert!(CALLS==1&&MCALLS==1);
   assert!(u64::from(result.0)==(2*u64::from(SQUARE)+2147483647-1)%2147483647);
  }
 }
'''
new=s[:at]+t+s[at:]
(E/'NBS_line.patch').write_text(''.join(difflib.unified_diff(s.splitlines(True),new.splitlines(True),fromfile='a/'+p,tofile='b/'+p)))
