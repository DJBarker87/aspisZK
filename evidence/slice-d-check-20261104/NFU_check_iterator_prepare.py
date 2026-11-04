from pathlib import Path
import json
from NFU_add_inputs import update
E=Path(__file__).resolve().parent;p='crates/aspis-r1-cost-probe/src/NFU_compact.rs';s=json.loads((E/'NFU_NATIVE_INPUTS.json').read_text())[p]
s+='''
// Arbitrary iterator pre-state; no prior decoding or whole-buffer loop.
#[kani::proof] #[kani::unwind(3)]
fn check_iterator(){let b:[u8;464]=kani::any();let i:usize=kani::any();kani::assume(i<=29);let mut it=b[16*i..].chunks_exact(16);let mut exact=it.len()==29-i&&it.remainder().is_empty();match it.next(){None=>{exact&=i==29&&it.is_empty();},Some(c)=>{exact&=i<29&&c.len()==16&&core::ptr::eq(c.as_ptr(),b[16*i..].as_ptr())&&it.len()==29-(i+1);match it.next(){None=>exact&=i+1==29,Some(next)=>exact&=i+1<29&&core::ptr::eq(next.as_ptr(),b[16*(i+1)..].as_ptr())};}}assert!(exact != cfg!(NFU_invert));}
'''
# ExactSizeIterator::is_empty is unstable; use the same zero-length statement.
s=s.replace('it.is_empty()','it.len()==0')
update({p:s},'NFU_check_iterator')
