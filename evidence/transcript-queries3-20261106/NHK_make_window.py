"""Split failed contract snapshot into a direct SAME-array window observation.
No renamed verdict: retains NHK_contains / NHK_contains_contract identifiers.
"""
from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent
n=int(sys.argv[1]);width=int(sys.argv[2]) if len(sys.argv)>2 else n
assert 1<=width<=n<=22
# n is the source active length; width selects one contiguous observation window.
# Full width retains offset0; split width quantifies every fitting offset.
limit=0 if width==n else n-width
pred=' || '.join(f'a[offset+{i}]==x' for i in range(width))
canon=' && '.join(f'a[{i}]<(1<<18)' for i in range(22))
inactive=' && '.join(f'a[{i}]==0' for i in range(n,22)) or 'true'
s='''use super::*;
fn NHK_contains(a:&[u32;22],offset:usize,x:u32)->bool {
 let result=a[offset..offset+WIDTH].contains(&x);
 #[cfg(not(NHK_invert))] {result}
 #[cfg(NHK_invert)] {!result}
}
#[kani::proof] #[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHK_contains_contract() {
 let a:[u32;22]=kani::any();let x:u32=kani::any();let offset:usize=kani::any();
 kani::assume(offset<=LIMIT && x<(1<<18) && CANON && INACTIVE);
 let expected=PRED;
 let result=NHK_contains(&a,offset,x);
 assert!(result==expected);
}
'''.replace('WIDTH',str(width)).replace('LIMIT',str(limit)).replace('CANON',canon).replace('INACTIVE',inactive).replace('PRED',pred)
(E/'NHK_constant_contains.rs.txt').write_text(s)
(E/'NHK_CONSTANT_CONTAINS.json').write_text(json.dumps(dict(length=n,width=width,offset_max=limit,shape='direct borrowed observation, no function-contract saved-array snapshot',property='actual Std.contains window == scalar disjunction of SAME window',domain='canonical22, inactive zero after active length, x18',credit='full length only if width==length; smaller window requires native/cohort composition'),indent=2)+'\n')
