from pathlib import Path
import json,subprocess,difflib,sys,re
E=Path(__file__).resolve().parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';mode=sys.argv[1]
assert mode in ['constructor','constructor-negative','request','request-negative']
if mode.startswith('request'):
 subprocess.run([sys.executable,str(E/'NFO_full_native.py'),'args'],check=True)
 source=json.loads((E/'NFO_CURRENT.json').read_text())['source']
 source=re.sub(r'assert!\(instruction\.accounts\[self\.meta\][^;]+;','',source)
 source=re.sub(r'assert!\(infos\[self\.meta\][^;]+;','',source)
 assert 'instruction.accounts[self.meta]' not in source and 'infos[self.meta]' not in source
 if mode.endswith('negative'):source=source.replace('instruction.data[self.j]==self.request_byte','instruction.data[self.j]==(self.request_byte^1)')
else:
 source=r'''use super::*;
#[kani::proof]
#[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFO_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NFO_KMX::KMX_copy_from_slice)]
fn association(){let key=Pubkey::new_from_array(kani::any());let signer:bool=kani::any();let j:usize=kani::any();kani::assume(j<32);let byte=key.to_bytes()[j];let mut meta=AccountMeta::new_readonly(key,signer);assert!(meta.pubkey.to_bytes()[j]==byte&&meta.is_signer==signer&&!meta.is_writable);}
'''
 if mode.endswith('negative'):source=source.replace('assert!(meta.pubkey', 'let mut wrong=meta.pubkey.to_bytes();wrong[j]^=1;meta.pubkey=Pubkey::new_from_array(wrong);assert!(meta.pubkey')
patch=''
for p in ['programs/aspis-pool/src/pair_forest_dispatch.rs','programs/aspis-pool/src/lib.rs']:
 frozen=subprocess.check_output(['git','show',REV+':'+p],text=True)
 hook=frozen+'\n#[cfg(kani)]\n#[path="NFO_read.rs"]\nmod NFO_read;\n' if p.endswith('pair_forest_dispatch.rs') else '#![cfg_attr(kani, feature(allocator_api))]\n'+frozen+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NFO_KMX;\n'
 patch+=''.join(difflib.unified_diff(frozen.splitlines(True),hook.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
p='programs/aspis-pool/src/NFO_read.rs';patch+='--- /dev/null\n+++ b/'+p+'\n@@ -0,0 +1,'+str(len(source.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in source.splitlines())
(E/'NFO_native.patch').write_text(patch);(E/'NFO_CURRENT.json').write_text(json.dumps(dict(mode=mode,source=source,classification='partial independent constructor/request forwarding; NOT a repair or closure of K056 metadata association'),indent=1)+'\n')
