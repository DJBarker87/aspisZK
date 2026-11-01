"""Re-establish the rule16-suspended serializer with a static-free module."""
from pathlib import Path
import difflib,subprocess,sys,json
from NEJ_patch_inputs import oracle_parts
E=Path(__file__).resolve().parent;mode=sys.argv[1];assert mode in ['positive','negative']
P=E.parent/'slice-s-compose2-20261029'
patch=(P/('NEE_K005-NEE_native_contracts.patch' if mode=='positive' else 'NEE_K006-NEE_native_contracts.patch')).read_text()
path='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs'
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],text=True)
changed=frozen+'\n#[cfg(kani)]\n#[path="NEJ_oracle.rs"]\nmod NEJ_oracle;\n'
patch+=''.join(difflib.unified_diff(frozen.splitlines(True),changed.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
base,hook=oracle_parts();body=base+'''#[kani::proof_for_contract(aspis_core::field::M31::to_le_bytes)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn frame_m31(){let x=aspis_core::field::M31(kani::any());let _=x.to_le_bytes();}
'''
assert 'static mut' not in body
(E/'NEJ_native_contracts.patch').write_text(patch)
(E/'NEJ_oracle.patch').write_text('--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEJ_oracle.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+s+'\n' for s in body.splitlines())+hook)
(E/'NEJ_CONTRACT_ERASURE.json').write_text(json.dumps(dict(case='m31',control=mode,actual_frozen_body_unchanged=True,original_property='full raw32 serializer equality and empty modifies; no static declarations',harness='pool_v1::pair_forest_terminal::NEJ_oracle::frame_m31'),indent=1)+'\n')
