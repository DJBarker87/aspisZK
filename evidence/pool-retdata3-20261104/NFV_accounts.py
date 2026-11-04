from pathlib import Path
import json,difflib,subprocess,sys
E=Path(__file__).resolve().parent
kind,index,control=sys.argv[1:4];index=int(index);assert kind in ['meta','info','meta-byte','info-byte'];assert 0<=index<6;assert control in ['positive','negative']
base=json.loads((E.parent/'pool-retdata-20261104/NFO_K056-shape.json').read_text())['source'];s=base
meta='assert!(instruction.accounts[self.meta].pubkey.to_bytes()==self.keys[self.meta]&&!instruction.accounts[self.meta].is_signer&&!instruction.accounts[self.meta].is_writable);'
infos='assert!(infos[self.meta].key.to_bytes()==self.keys[self.meta]&&infos[7].key==&self.selected);'
if kind.startswith('meta'):s=s.replace(infos,'')
else:s=s.replace(meta,'')
attrs='#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFO_KMX::KMX_copy_nonoverlapping)]\n#[kani::stub(<[u8]>::copy_from_slice,crate::NFO_KMX::KMX_copy_from_slice)]\n'
assert attrs in s;s=s.replace(attrs,attrs+'#[kani::stub(alloc::alloc::realloc,crate::NFO_KMX::KMX_realloc)]\n')
# AccountInfo target layout is separately recorded by the native layout probe.
bound=337
s=s.replace('#[kani::unwind(34)]',f'#[kani::unwind({bound})]').replace('let meta:usize=kani::any();kani::assume(meta<7);',f'let meta:usize={index};')
if kind.endswith('-byte'):
 expr='instruction.accounts[self.meta].pubkey.to_bytes()' if kind.startswith('meta') else 'infos[self.meta].key.to_bytes()'
 s=s.replace(expr+'==self.keys[self.meta]',expr+'[self.j%32]==self.keys[self.meta][self.j%32]')
if control=='negative':
 if kind.endswith('-byte'):s=s.replace('==self.keys[self.meta][self.j%32]','==(self.keys[self.meta][self.j%32]^1)')
 else:s=s.replace('==self.keys[self.meta]','=={let mut wrong=self.keys[self.meta];wrong[0]^=1;wrong}')
patch=''
for p in ['programs/aspis-pool/src/pair_forest_dispatch.rs','programs/aspis-pool/src/lib.rs']:
 f=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
 hook=f+'\n#[cfg(kani)]\n#[path="NFO_read.rs"]\nmod NFO_read;\n' if p.endswith('pair_forest_dispatch.rs') else '#![cfg_attr(kani, feature(allocator_api))]\n'+f+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NFO_KMX;\n'
 patch+=''.join(difflib.unified_diff(f.splitlines(True),hook.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
p='programs/aspis-pool/src/NFO_read.rs';patch+='--- /dev/null\n+++ b/'+p+'\n@@ -0,0 +1,'+str(len(s.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in s.splitlines())
(E/'NFV_native.patch').write_text(patch);(E/'NFV_CURRENT.json').write_text(json.dumps(dict(kind=kind,index=index,control=control,unwind=bound,source=s,base='NFO_K056',ruling='af'),indent=1)+'\n')
