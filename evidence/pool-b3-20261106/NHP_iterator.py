"""One native std iterator step on a complete arbitrary caller-width backing array."""
from pathlib import Path
import sys,subprocess,json,difflib
E=Path(__file__).resolve().parent;mode=sys.argv[1];n=int(sys.argv[2]);assert n in [32,36,82,165] and mode in ['positive','negative']
source='''use super::*;
#[kani::proof]
#[kani::unwind(UNWIND)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NHP_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NHP_KMX::KMX_copy_from_slice)]
#[kani::stub(alloc::alloc::realloc,crate::NHP_KMX::KMX_realloc)]
fn association(){
 let input:[u8;WIDTH]=kani::any();let begin:usize=kani::any();let end:usize=kani::any();kani::assume(begin<=end&&end<=WIDTH);
 let q:usize=kani::any();kani::assume(q<WIDTH);let before=input[q];
 let mut iter=input[begin..end].iter();let observed=iter.next().map(|b|(*b,b as *const u8));
 if begin<end {
  assert!(observed==Some((BYTE,input.as_ptr().wrapping_add(begin))));
  assert!(iter.as_slice().len()==end-begin-1);assert!(iter.as_slice().as_ptr()==input.as_ptr().wrapping_add(begin+1));
 } else {assert!(observed.is_none());assert!(iter.as_slice().len()==0);assert!(iter.as_slice().as_ptr()==input.as_ptr().wrapping_add(end));}
 assert!(input[q]==before);
}
'''.replace('UNWIND',str(n+2)).replace('WIDTH',str(n)).replace('BYTE','input[begin]' if mode=='positive' else 'input[begin]^1')
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';read=lambda p:subprocess.check_output(['git','show',rev+':'+p],text=True);patch=''
for p in ['programs/aspis-pool/src/vault.rs','programs/aspis-pool/src/lib.rs']:
 before=read(p)
 after=before+'\n#[cfg(kani)]\nmod NHP_iterator {\n'+source+'}\n' if p.endswith('/vault.rs') else '#![cfg_attr(kani, feature(allocator_api))]\n'+before+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NHP_KMX;\n'
 patch+=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
(E/'NHP_native.patch').write_text(patch);(E/'NHP_CURRENT.json').write_text(json.dumps(dict(kind='fixed caller-width iterator '+str(n),mode=mode,source=source,domain=f'Every {n}-byte backing array, every residual begin..end subwindow, every selected whole-array frame cell; exactly one native next() call',modifies=['private iterator pointer/length only'],production_credit=False,remaining='actual all/any loop-state association, same AccountInfo/decoded request caller and borrowed-carrier domain; NHC trace/value/count induction reused'),indent=1)+'\n')
print('vault::NHP_iterator::association')
