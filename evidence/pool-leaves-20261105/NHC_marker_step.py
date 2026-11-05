"""One native Iterator::all iteration, not a whole-buffer predicate probe."""
from pathlib import Path
import sys,subprocess,difflib,json,re,hashlib
E=Path(__file__).resolve().parent;mode=sys.argv[1];assert mode in ['positive','negative']
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';read=lambda p:subprocess.check_output(['git','show',rev+':'+p],text=True)
src=read('programs/aspis-pool/src/nullifier.rs');fragment=re.search(r'\.all\((\|byte\|\s*\*byte\s*==\s*0)\)',src).group(1)
s='''use super::*;
#[kani::proof]
#[kani::unwind(3)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFO_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NFO_KMX::KMX_copy_from_slice)]
#[kani::stub(alloc::alloc::realloc,crate::NFO_KMX::KMX_realloc)]
fn association(){
 let byte:u8=kani::any();let available:bool=kani::any();
 let index:usize=kani::any();let total:usize=kani::any();kani::assume(index<=total);kani::assume(available==(index<total));
 let one=[byte];let window=if available{&one[..]}else{&one[..0]};
 let mut calls=0usize;let mut observed=None;
 let mut it=window.iter();
 let mut result=it.all(|byte|{calls+=1;observed=Some(*byte);PRED});
 CORRUPT
 assert!(result==(!available||byte==0));
 assert!(calls==usize::from(available));
 assert!(observed==if available{Some(byte)}else{None});
 assert!(it.as_slice().is_empty());
 let next=if available{index+1}else{index};
 assert!(next<=total);assert!(next==index+usize::from(available));
}
'''.replace('PRED',fragment.split('|',2)[2].strip()).replace('CORRUPT','if available{observed=Some(byte^1);}' if mode=='negative' else '')
patch=''
for p in ['programs/aspis-pool/src/nullifier.rs','programs/aspis-pool/src/lib.rs']:
 f=read(p);after=f+'\n#[cfg(kani)]\n#[path="NHC_MarkerStep.rs"]\nmod NHC_MarkerStep;\n' if p.endswith('nullifier.rs') else '#![cfg_attr(kani, feature(allocator_api))]\n'+f+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NFO_KMX;\n'
 patch+=''.join(difflib.unified_diff(f.splitlines(True),after.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
p='programs/aspis-pool/src/NHC_MarkerStep.rs';patch+='--- /dev/null\n+++ b/'+p+'\n@@ -0,0 +1,'+str(len(s.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in s.splitlines())
(E/'NHC_native.patch').write_text(patch);(E/'NHC_CURRENT.json').write_text(json.dumps(dict(kind='marker one iteration',mode=mode,source=s,domain='index<=total, available iff index<total; arbitrary selected byte; one native Iterator::all step; unconsumed suffix/frame association remains to prove',modifies=['local iterator','local call record'],production_credit=False),indent=1)+'\n')
print('nullifier::NHC_MarkerStep::association')
