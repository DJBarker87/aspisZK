"""One arbitrary-offset native window split. Native semantics on both subwindows.
Full windows that timed out under contract capture are not retried unchanged.
"""
from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent
n=int(sys.argv[1]);cut=int(sys.argv[2]);assert 0<cut<n<=21
canon=' && '.join(f'a[{i}]<(1<<18)' for i in range(22))
s='''use super::*;
fn NHK_contains(a:&[u32;22],offset:usize,x:u32)->bool {
 let result=a[offset..offset+LEN].contains(&x);
 #[cfg(not(NHK_invert))] {result}
 #[cfg(NHK_invert)] {!result}
}
#[kani::proof] #[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHK_contains_contract() {
 let a:[u32;22]=kani::any();let x:u32=kani::any();let offset:usize=kani::any();
 kani::assume(offset<=LIMIT && x<(1<<18) && CANON);
 let left=a[offset..offset+CUT].contains(&x);
 let right=a[offset+CUT..offset+LEN].contains(&x);
 let result=NHK_contains(&a,offset,x);
 assert!(result==(left || right));
}
'''.replace('CANON',canon).replace('LIMIT',str(22-n)).replace('CUT',str(cut)).replace('LEN',str(n))
s=s.replace('let a:[u32;22]=kani::any();', 'let a:[u32;22]=['+', '.join(['kani::any()']*22)+'];')
(E/'NHK_constant_contains.rs.txt').write_text(s)
(E/'NHK_CONSTANT_CONTAINS.json').write_text(json.dumps(dict(length=n,cut=cut,offset_max=22-n,shape='native contiguous window composition with no saved-array snapshot',property='native full window == native prefix OR native suffix on SAME array',domain='canonical22 and x18; no inactive-zero restriction',remaining='scalar laws on both smaller native windows and Lean list frame/disjoint composition'),indent=2)+'\n')
