"""Source prefix at its actual fixed start; no aggregate snapshots.
Two scalar reference windows together cover EVERY cell in the native prefix.
"""
from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent;n=int(sys.argv[1]);assert 1<=n<22
cut=min(8,n)
left=' | '.join(f'(a[{i}]==x)' for i in range(cut)) or 'false'
right=' | '.join(f'(a[{i}]==x)' for i in range(cut,n)) or 'false'
init=', '.join(['kani::any()']*22)
s=f'''use super::*;
fn NHK_contains(a:&[u32;22],x:u32)->bool {{
 let result=a[..{n}].contains(&x);
 #[cfg(not(NHK_invert))] {{result}}
 #[cfg(NHK_invert)] {{!result}}
}}
#[kani::proof] #[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHK_contains_contract() {{
 let a:[u32;22]=[{init}];let x:u32=kani::any();
 let left={left};let right={right};
 let expected=left || right;let result=NHK_contains(&a,x);
 assert!(result==expected);
}}
'''
(E/'NHK_constant_contains.rs.txt').write_text(s)
(E/'NHK_CONSTANT_CONTAINS.json').write_text(json.dumps(dict(length=n,cut=cut,offset=0,shape='direct read-only fixed native prefix, two scalar specification windows, no saved-array snapshot',domain='all22 arbitrary u32 cells and arbitrary u32 x; stronger than canonical caller domain in coverage',actual='unchanged Std.contains on the entire prefix',callee_stubbing='none except mandated KMX copy builtin',remaining='paired control and NHB prefix predicate / NHK_WindowLaws adapter; no successful run premise'),indent=2)+'\n')
