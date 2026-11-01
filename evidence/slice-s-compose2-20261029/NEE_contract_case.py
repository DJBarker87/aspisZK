"""Prepare cfg(kani)-only actual frozen function contract, with exact erasure."""
from pathlib import Path
import difflib,hashlib,json,subprocess,sys
from NEE_patch_inputs import oracle_parts
E=Path(__file__).resolve().parent
case,control=sys.argv[1:];assert case=='m31';assert control in {'positive','negative'}
p='crates/aspis-core/src/field.rs'
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
needle='    pub fn to_le_bytes(self) -> [u8; 4] {'
op='==' if control=='positive' else '!='
attrs=f'    #[cfg_attr(kani,kani::modifies())]\n    #[cfg_attr(kani,kani::ensures(|r| *r {op} self.0.to_le_bytes()))]\n'
assert frozen.count(needle)==1
changed=frozen.replace(needle,attrs+needle)
assert changed.replace(attrs,'')==frozen
patch=''.join(difflib.unified_diff(frozen.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
(E/'NEE_native_contracts.patch').write_text(patch)
body,hook=oracle_parts()
body+='''#[kani::proof_for_contract(aspis_core::field::M31::to_le_bytes)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn frame_m31(){let x=aspis_core::field::M31(kani::any());let _=x.to_le_bytes();}
'''
(E/'NEE_oracle.patch').write_text('--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEE_oracle.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines())+hook)
(E/'NEE_CONTRACT_ERASURE.json').write_text(json.dumps(dict(case=case,control=control,actual_frozen_body_unchanged=True,sha256=hashlib.sha256(frozen.encode()).hexdigest(),contract_patch_sha256=hashlib.sha256(patch.encode()).hexdigest()),indent=1)+'\n')
