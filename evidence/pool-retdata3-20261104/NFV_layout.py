from pathlib import Path
import subprocess,difflib,sys,json
E=Path(__file__).resolve().parent;mode=sys.argv[1];assert mode in ['positive','negative']
s='use super::*;\n#[kani::proof]\nfn association(){assert!(core::mem::size_of::<AccountMeta>()=='+('35' if mode=='negative' else '34')+');assert!(core::mem::size_of::<AccountInfo<\'_>>()==48);}\n'
patch=''
for p in ['programs/aspis-pool/src/pair_forest_dispatch.rs','programs/aspis-pool/src/lib.rs']:
 f=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
 hook=f+'\n#[cfg(kani)]\n#[path="NFO_read.rs"]\nmod NFO_read;\n' if p.endswith('pair_forest_dispatch.rs') else '#![cfg_attr(kani, feature(allocator_api))]\n'+f+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NFO_KMX;\n'
 patch+=''.join(difflib.unified_diff(f.splitlines(True),hook.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
p='programs/aspis-pool/src/NFO_read.rs';patch+='--- /dev/null\n+++ b/'+p+'\n@@ -0,0 +1,'+str(len(s.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in s.splitlines())
(E/'NFV_native.patch').write_text(patch);(E/'NFV_CURRENT.json').write_text(json.dumps(dict(mode='layout-'+mode,source=s,classification='host native layouts only, deployed Pool features; no copy builtin reached by property'),indent=1)+'\n')
