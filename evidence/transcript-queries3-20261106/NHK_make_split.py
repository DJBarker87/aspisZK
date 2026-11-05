"""Native full-length composition against two smaller native windows after timeout."""
from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent
n=int(sys.argv[1]);cut=int(sys.argv[2]);assert 0<cut<n<22
canon=' && '.join(f'a[{i}]<(1<<18)' for i in range(22))
inactive=' && '.join(f'a[{i}]==0' for i in range(n,22))
s='''use super::*;
fn NHK_contains(a:&[u32;22],x:u32)->bool {
 let result=a[..N].contains(&x);
 #[cfg(not(NHK_invert))] {result}
 #[cfg(NHK_invert)] {!result}
}
#[kani::proof] #[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHK_contains_contract() {
 let a:[u32;22]=kani::any();let x:u32=kani::any();
 kani::assume(x<(1<<18) && CANON && INACTIVE);
 let left=a[..CUT].contains(&x);
 let right=a[CUT..N].contains(&x);
 let result=NHK_contains(&a,x);
 assert!(result==(left || right));
}
'''.replace('CANON',canon).replace('INACTIVE',inactive).replace('CUT',str(cut)).replace('N]',str(n)+']')
(E/'NHK_constant_contains.rs.txt').write_text(s)
(E/'NHK_CONSTANT_CONTAINS.json').write_text(json.dumps(dict(length=n,cut=cut,shape='full native membership == disjunction of native prefix/suffix windows; no saved-array snapshot',domain='same canonical22 and inactive-zero caller domain',remaining='both native windows need scalar membership laws; Lean append law joins same prefix'),indent=2)+'\n')
