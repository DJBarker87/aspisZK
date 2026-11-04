from pathlib import Path
import json,sys,subprocess,difflib
E=Path(__file__).resolve().parent;mode=sys.argv[1];assert mode in ['byte','byte-negative','error','error-negative']
base=json.loads((E.parent/'pool-retdata2-20261104/NFR_K034-shape.json').read_text())['source']
s=base[:base.index('fn observe')]
s+='''#[kani::proof]
#[kani::unwind(793)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFO_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NFO_KMX::KMX_copy_from_slice)]
#[kani::stub(alloc::alloc::realloc,crate::NFO_KMX::KMX_realloc)]
fn association(){
 let r=result();let j:usize=kani::any();kani::assume(j<792);
 let expected=encode_pool_v1_pair_forest_terminal_result_v1(&r);
 let actual=terminal_result_bytes_box_v1(&r);
 match (expected,actual){
  (Ok(bytes),Ok(boxed))=>{CHECK_BYTE},
  (Err(_),Err(error))=>{CHECK_ERROR},
  _=>panic!("native helper changed Result variant")
 }
}
'''
byte='assert!(boxed[j]==bytes[j]);' if mode=='byte' else 'assert!(boxed[j]==(bytes[j]^1));' if mode=='byte-negative' else ''
error='assert!(error==PoolV1ProgramError::InvalidVerifierReturnData.into());' if mode=='error' else 'assert!(error!=PoolV1ProgramError::InvalidVerifierReturnData.into());' if mode=='error-negative' else ''
s=s.replace('CHECK_BYTE',byte).replace('CHECK_ERROR',error)
patch=''
for p in ['programs/aspis-pool/src/pair_forest.rs','programs/aspis-pool/src/lib.rs']:
 f=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
 hook=f+'\n#[cfg(kani)]\n#[path="NFV_Helper.rs"]\nmod NFV_Helper;\n' if p.endswith('pair_forest.rs') else '#![cfg_attr(kani, feature(allocator_api))]\n'+f+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NFO_KMX;\n'
 patch+=''.join(difflib.unified_diff(f.splitlines(True),hook.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
p='programs/aspis-pool/src/NFV_Helper.rs';patch+='--- /dev/null\n+++ b/'+p+'\n@@ -0,0 +1,'+str(len(s.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in s.splitlines())
(E/'NFV_native.patch').write_text(patch);(E/'NFV_CURRENT.json').write_text(json.dumps(dict(mode=mode,source=s,classification='actual frozen helper with actual encoder, observation split; no repr(C) log, no encoder or field stub',base='NFR_K034 arbitrary result constructor only'),indent=1)+'\n')
