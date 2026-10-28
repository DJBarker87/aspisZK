from pathlib import Path
import sys
sys.dont_write_bytecode=True
from NBP_patch_sources import added_patch,pieces
import difflib
E=Path(__file__).resolve().parent
s='''use core::fmt::Write;
struct NBP_Writer { index:usize, seen:usize, expected:&'static str }
impl Write for NBP_Writer {
 fn write_str(&mut self,s:&str)->core::fmt::Result {
  let n=s.len();
  if self.index>=self.seen && self.index-self.seen<n {
   assert!(s.as_bytes()[self.index-self.seen]==self.expected.as_bytes()[self.index]);
  }
  self.seen+=n;
  Ok(())
 }
}
'''
for v in ['Parse','Semantic','Transcript','Relation','Merkle','Query','Checkpoint','Allocation']:
 for part in ['debug','message']:
  exp=v if part=='debug' else 'r1:error:'+v
  fmt='{:?}' if part=='debug' else 'r1:error:{:?}'
  s+=f'''#[kani::proof]
#[kani::unwind(64)]
fn NBP_{part}_{v}() {{
 let i:usize=kani::any();kani::assume(i<{len(exp)});
 let mut w=NBP_Writer{{index:i,seen:0,expected:"{exp}"}};
 assert!(write!(&mut w,"{fmt}",aspis_r1_cost_probe::verifier::Error::{v}).is_ok());
 assert!(w.seen=={len(exp)});
 kani::cover!(i=={len(exp)-1});
}}
'''
p='programs/r1-cost-probe/src/NBP_error.rs';old=added_patch(E/'NBP_error.patch','/NBP_error.rs');new=old+s
(E/'NBP_components.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+p,tofile='b/'+p)))
