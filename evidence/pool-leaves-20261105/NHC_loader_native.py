"""Actual frozen Bool helper contract, on every 32-byte owner value."""
from pathlib import Path
import sys,subprocess,difflib,json
E=Path(__file__).resolve().parent;mode=sys.argv[1];assert mode in ['positive','negative']
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';read=lambda p:subprocess.check_output(['git','show',rev+':'+p],text=True)
reference=(E.parent/'pool-prefix-20261105/NGG_E001/NGG_reference.rs').read_text()
model=next(l for l in reference.splitlines() if l.startswith('pub fn supported_loader('))
s='use super::*;\npub type Key=[u8;32];\n'+model+'\n'
s+='''pub(super) fn reference(owner:&Pubkey)->bool {
 let r=supported_loader(&owner.to_bytes(),&[bpf_loader::id().to_bytes(),bpf_loader_upgradeable::id().to_bytes(),loader_v4::id().to_bytes()]);
 RETURN
}
#[kani::proof_for_contract(super::supported_loader)]
#[kani::unwind(33)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFO_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NFO_KMX::KMX_copy_from_slice)]
#[kani::stub(alloc::alloc::realloc,crate::NFO_KMX::KMX_realloc)]
fn association(){let owner=Pubkey::new_from_array(kani::any());let actual=super::supported_loader(&owner);assert!(actual==reference(&owner));}
'''.replace('RETURN','r' if mode=='positive' else '!r')
patch=''
for p in ['programs/aspis-pool/src/pair_forest_dispatch.rs','programs/aspis-pool/src/lib.rs']:
 f=read(p)
 if p.endswith('pair_forest_dispatch.rs'):
  after=f.replace('fn supported_loader(owner:', '#[cfg_attr(kani,kani::requires(true))]\n#[cfg_attr(kani,kani::ensures(|r| *r == NHC_Loader::reference(owner)))]\n#[cfg_attr(kani,kani::modifies())]\nfn supported_loader(owner:')+'\n#[cfg(kani)]\n#[path="NHC_Loader.rs"]\nmod NHC_Loader;\n'
 else:after='#![cfg_attr(kani, feature(allocator_api))]\n'+f+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NFO_KMX;\n'
 patch+=''.join(difflib.unified_diff(f.splitlines(True),after.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
p='programs/aspis-pool/src/NHC_Loader.rs';patch+='--- /dev/null\n+++ b/'+p+'\n@@ -0,0 +1,'+str(len(s.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in s.splitlines())
(E/'NHC_native.patch').write_text(patch);(E/'NHC_CURRENT.json').write_text(json.dumps(dict(kind='actual supported_loader Bool contract',mode=mode,source=s,domain='every Pubkey owner (all 32-byte arrays); valid immutable Rust reference',modifies=[],lean_theorem='NHC_NGG_Loader.result',production_credit=False,copy_negative='same-source inverted reference in matched configuration'),indent=1)+'\n')
print('pair_forest_dispatch::NHC_Loader::association')
