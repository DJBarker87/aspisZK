"""Source-exact one-iteration bodies; full pack/source-to-model association remains open."""
from pathlib import Path
import re,sys,json,subprocess,difflib,hashlib
E=Path(__file__).resolve().parent;mode,kind=sys.argv[1:];assert mode in ['positive','negative'] and kind in ['byte','group']
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';path='programs/aspis-pool/src/nullifier.rs';original=subprocess.check_output(['git','show',rev+':'+path],text=True)
loop=re.search(r'while '+('byte < 7' if kind=='byte' else 'group < 8')+r' \{(.*?)\n        \}',original,re.S).group(1).strip()+'\n'
source='''use super::*;
#[kani::proof]
#[kani::unwind(33)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NHP_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NHP_KMX::KMX_copy_from_slice)]
#[kani::stub(alloc::alloc::realloc,crate::NHP_KMX::KMX_realloc)]
fn association(){
 let digest:[u8;32]=kani::any();let mut seed:[u8;32]=kani::any();
 let chunk:usize=kani::any();kani::assume(chunk<4);let mut word:u64=kani::any();kani::assume(word<(1u64<<56));
 let q:usize=kani::any();kani::assume(q<32);let prior_digest=digest[q];let prior_seed=seed[q];let prior_word=word;
 SETUP
 LOOP
 CHECK
 assert!(digest[q]==prior_digest);
}
'''
if kind=='byte':
 setup='let mut byte:usize=kani::any();kani::assume(byte<7);let prior_byte=byte;let expected=word*256+u64::from(digest[7*chunk+byte]);'
 check='assert!(byte==prior_byte+1);assert!(word=='+('expected' if mode=='positive' else '(expected^1)')+');assert!(seed[q]==prior_seed);'
else:
 setup='let mut group:usize=kani::any();kani::assume(group<8);let prior_group=group;let position=8*chunk+group;'
 setup+='let quotient=match group {'+''.join(f'{g}=>word/{1<<(7*(7-g))}u64,' for g in range(8))+'_=>unreachable!()};let expected=(quotient%128) as u8;'
 check='assert!(group==prior_group+1);assert!(word==prior_word);assert!(seed[position]=='+('expected' if mode=='positive' else '(expected^1)')+');assert!(seed[position]<128);assert!(seed[q]==if q==position {expected}else{prior_seed});'
source=source.replace('SETUP',setup).replace('LOOP',loop).replace('CHECK',check)
patch=''
for p in [path,'programs/aspis-pool/src/lib.rs']:
 before=subprocess.check_output(['git','show',rev+':'+p],text=True)
 after=before+'\n#[cfg(kani)]\nmod NHP_pack_step {\n'+source+'}\n' if p==path else '#![cfg_attr(kani, feature(allocator_api))]\n'+before+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NHP_KMX;\n'
 patch+=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
(E/'NHP_native.patch').write_text(patch);(E/'NHP_CURRENT.json').write_text(json.dumps(dict(kind='marker pack '+kind+' source iteration',mode=mode,source=source,frozen_statement=loop,frozen_statement_sha256=hashlib.sha256(loop.encode()).hexdigest(),domain='Arbitrary full32-byte digest/seed, chunk<4, byte<7 or group<8, word<2^56, arbitrary whole-array frame query; exactly one copied frozen loop iteration',modifies=['local word/byte counter' if kind=='byte' else 'one seed cell/group counter'],production_credit=False,remaining='cut-to-parent native association, complete nested-loop/body correspondence and adopted pack model; no whole-buffer credit'),indent=1)+'\n')
print('nullifier::NHP_pack_step::association')
