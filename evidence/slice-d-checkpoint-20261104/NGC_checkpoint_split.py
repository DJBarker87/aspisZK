from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;x=json.loads((E/'NGC_NATIVE_INPUTS.json').read_text());n='crates/aspis-r1-cost-probe/src/NGC_windows.rs';s=x[n]
def replace_body(s,name,replacement):
 start=s.index('fn '+name+'(){');b=start+len('fn '+name+'(){');i=b;depth=1
 while depth:depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[:b]+replacement+s[i-1:]
s+='''
// Arbitrary observed byte in an allocated 1768-byte capacity. Vec::push on
// spare capacity never reads the other prefix cells; this is the one-window
// prestate used for the frame composition, not a whole-buffer copy proof.
fn byte_prestate(len:usize,observed:usize,old:u8)->Vec<u8>{unsafe{let layout=alloc::alloc::Layout::array::<u8>(1768).unwrap();let ptr=alloc::alloc::alloc_zeroed(layout);kani::assume(!ptr.is_null());ptr.add(observed).write(old);Vec::from_raw_parts(ptr,len,1768)}}
'''
s=replace_body(s,'checkpoint_transition','''let prefix:usize=kani::any();let observed:usize=kani::any();let index:usize=kani::any();let width:usize=kani::any();kani::assume(width<=32&&index<width&&prefix<1768&&observed<=prefix);let old:u8=kani::any();let source:[u8;32]=kani::any();let mut out=byte_prestate(prefix,observed,old);let ptr=out.as_ptr();let mut cursor=index;
// ONE exact KMX_extend_from_slice body iteration.
out.push(source[cursor]);cursor+=1;
assert!(out.len()==prefix+1&&out.as_ptr()==ptr&&cursor==index+1);let expected=if observed<prefix{old}else{source[index]};assert!(out[observed]==if cfg!(NGC_invert){expected^1}else{expected});''')
s=replace_body(s,'checkpoint_copy_positive','''let index:usize=kani::any();let observed:usize=kani::any();kani::assume(index<1768&&observed<1768);let old:u8=kani::any();let source:u8=kani::any();let mut out=byte_prestate(1768,observed,old);unsafe{core::ptr::copy_nonoverlapping(&source,out.as_mut_ptr().add(index),1)};assert!(out[index]==source);if observed!=index{assert!(out[observed]==old);}''')
s=replace_body(s,'checkpoint_copy_negative','''let index:usize=kani::any();let observed:usize=kani::any();kani::assume(index<1768&&observed<1768);let old:u8=kani::any();let source:u8=kani::any();let mut out=byte_prestate(1768,observed,old);unsafe{core::ptr::copy_nonoverlapping(&source,out.as_mut_ptr().add(index),1)};assert!(out[index]!=source);if observed!=index{assert!(out[observed]==old);}''')
x[n]=s;(E/'NGC_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');p=json.loads((E/'NGC_SOURCE_PINS.json').read_text());p.update({n:hashlib.sha256(s.encode()).hexdigest()for n,s in x.items()});(E/'NGC_SOURCE_PINS.json').write_text(json.dumps(p,indent=1)+'\n')
(E/'NGC_CHECKPOINT_SPLIT.json').write_text(json.dumps(dict(old_attempt='NGC_K030',old_status='TIMEOUT; excluded',replacement='one exact KMX byte-push/cursor step; arbitrary observed prefix byte and appended byte in spare capacity; Lean finite byte induction and 116-emission composition',same_harness_name=True,timeout_unchanged_seconds=90,caps_unchanged=True),indent=1)+'\n')
