from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;x=json.loads((E/'NGC_NATIVE_INPUTS.json').read_text());n='crates/aspis-r1-cost-probe/src/NGC_windows.rs'
x[n]+='''
#[kani::proof] KMXL
fn checkpoint_transition(){let before:[u8;1768]=kani::any();let piece:[u8;32]=kani::any();let prefix:usize=kani::any();let width:usize=kani::any();let j:usize=kani::any();kani::assume(width<=32&&prefix<=1768-width&&j<prefix+width);let old=before[j];let mut out=Vec::from(before);out.truncate(prefix);let ptr=out.as_ptr();out.extend_from_slice(&piece[..width]);assert!(out.len()==prefix+width&&out.as_ptr()==ptr);let expected=if j<prefix{old}else{piece[j-prefix]};assert!(out[j]==if cfg!(NGC_invert){expected^1}else{expected});}
#[kani::proof] KMXL
fn checkpoint_copy_positive(){let before:[u8;1768]=kani::any();let j:usize=kani::any();kani::assume(j<1768);let expected=before[j];let out=Vec::from(before);assert!(out[j]==expected);}
#[kani::proof] KMXL
fn checkpoint_copy_negative(){let before:[u8;1768]=kani::any();let j:usize=kani::any();kani::assume(j<1768);let expected=before[j];let out=Vec::from(before);assert!(out[j]!=expected);}
'''.replace('KMXL','''#[kani::unwind(70)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]''')
(E/'NGC_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');p=json.loads((E/'NGC_SOURCE_PINS.json').read_text());p.update({n:hashlib.sha256(s.encode()).hexdigest()for n,s in x.items()});(E/'NGC_SOURCE_PINS.json').write_text(json.dumps(p,indent=1)+'\n')
