from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;x=json.loads((E/'NGC_NATIVE_INPUTS.json').read_text());n='crates/aspis-r1-cost-probe/src/NGC_windows.rs';s=x[n]
s+='''
// K066 replacement: one native std Vec::push, no Vec::resize bulk loop.
fn fill_push_window<T:Copy+PartialEq>(value:T,old:T){let prefix:usize=kani::any();let j:usize=kani::any();kani::assume(prefix<32768&&j<=prefix);let mut out=resize_prestate(prefix,j,old);let ptr=out.as_ptr();out.push(value);let want=if j<prefix{old}else{value};assert!((out.len()==prefix+1&&out.as_ptr()==ptr&&out[j]==want)!=cfg!(NGC_invert));}
'''
values={'u8':'kani::any::<u8>()','q':'kani::any::<K>()','raw':'kani::any::<[u64;4]>()','wide':'E::new(kani::any(),kani::any())'}
for typ,v in values.items():
 s+='\n#[kani::proof]\n#[kani::unwind(70)]\n#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]\n#[kani::stub(alloc::alloc::realloc,KMX_realloc)]\nfn fill_push_'+typ+'(){fill_push_window('+v+','+v+');}\n'
x[n]=s;(E/'NGC_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');p=json.loads((E/'NGC_SOURCE_PINS.json').read_text());p.update({n:hashlib.sha256(s.encode()).hexdigest()for n,s in x.items()});(E/'NGC_SOURCE_PINS.json').write_text(json.dumps(p,indent=1)+'\n')
(E/'NGC_HEAP_SPLIT.json').write_text(json.dumps(dict(excluded='NGC_K066 Vec::resize arbitrary-prefix loop timed out',replacement='One std Vec::push from arbitrary owned prefix with spare capacity, all four frozen types; fixed-value Lean induction and exact identity Clone; std resize call association remains retained realization',not_an_unchanged_rerun=True),indent=1)+'\n')
