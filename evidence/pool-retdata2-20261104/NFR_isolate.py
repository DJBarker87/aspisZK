from pathlib import Path
import json,difflib,subprocess,sys
E=Path(__file__).resolve().parent;O=E.parent/'pool-retdata-20261104'
mode=sys.argv[1];base=json.loads((O/'NFO_K056-shape.json').read_text())['source'];source=base
meta='assert!(instruction.accounts[self.meta].pubkey.to_bytes()==self.keys[self.meta]&&!instruction.accounts[self.meta].is_signer&&!instruction.accounts[self.meta].is_writable);'
infos='assert!(infos[self.meta].key.to_bytes()==self.keys[self.meta]&&infos[7].key==&self.selected);'
request='assert!(instruction.data.len()==320&&core::ptr::eq(instruction.data.as_ptr(),self.request)&&instruction.data[self.j]==self.request_byte);'
if mode=='no-infos':source=source.replace(infos,'')
elif mode=='no-meta':source=source.replace(meta,'')
elif mode=='meta-key':source=source.replace(infos,'').replace(meta,'assert!(instruction.accounts[self.meta].pubkey.to_bytes()==self.keys[self.meta]);')
elif mode=='meta-flags':source=source.replace(infos,'').replace(meta,'assert!(!instruction.accounts[self.meta].is_signer&&!instruction.accounts[self.meta].is_writable);')
elif mode=='info-key':source=source.replace(meta,'').replace(infos,'assert!(infos[self.meta].key.to_bytes()==self.keys[self.meta]);')
elif mode=='info-program':source=source.replace(meta,'').replace(infos,'assert!(infos[7].key==&self.selected);')
elif mode.startswith('no-infos-offset-') and not mode.endswith('negative'):
 source=source.replace(infos,'').replace('let meta:usize=kani::any();kani::assume(meta<7);','let meta:usize='+str(int(mode.split('-')[-1]))+';')
elif mode=='meta-flags-negative':source=source.replace(infos,'').replace(meta,'assert!(!instruction.accounts[self.meta].is_signer&&instruction.accounts[self.meta].is_writable);')
elif mode=='no-infos-offset-6-negative':source=source.replace(infos,'').replace('let meta:usize=kani::any();kani::assume(meta<7);','let meta:usize=6;').replace('self.keys[self.meta]&&!instruction','{let mut wrong=self.keys[self.meta];wrong[0]^=1;wrong}&&!instruction')
elif mode=='no-infos-no-readonly':source=source.replace(infos,'').replace('&&!instruction.accounts[self.meta].is_writable','')
elif mode=='no-infos-no-signer':source=source.replace(infos,'').replace('&&!instruction.accounts[self.meta].is_signer','')
elif mode.startswith('meta-byte'):
 source=source.replace(infos,'').replace('instruction.accounts[self.meta].pubkey.to_bytes()==self.keys[self.meta]', 'instruction.accounts[self.meta].pubkey.to_bytes()[self.j%32]==self.keys[self.meta][self.j%32]')
 if mode.endswith('negative'):source=source.replace('==self.keys[self.meta][self.j%32]', '==(self.keys[self.meta][self.j%32]^1)')
elif mode.startswith('info-byte'):
 source=source.replace(meta,'').replace('infos[self.meta].key.to_bytes()==self.keys[self.meta]', 'infos[self.meta].key.to_bytes()[self.j%32]==self.keys[self.meta][self.j%32]').replace('infos[7].key==&self.selected','infos[7].key.to_bytes()[self.j%32]==self.selected.to_bytes()[self.j%32]')
 if mode.endswith('negative'):source=source.replace('==self.keys[self.meta][self.j%32]', '==(self.keys[self.meta][self.j%32]^1)')
elif mode.startswith('info-key-offset-'):
 source=source.replace(meta,'').replace(infos,'assert!(infos[self.meta].key.to_bytes()==self.keys[self.meta]);').replace('let meta:usize=kani::any();kani::assume(meta<7);','let meta:usize=6;')
 if mode.endswith('negative'):source=source.replace('infos[self.meta].key.to_bytes()==self.keys[self.meta]', 'infos[self.meta].key.to_bytes()=={let mut wrong=self.keys[self.meta];wrong[0]^=1;wrong}')
elif mode=='info-program-negative':source=source.replace(meta,'').replace(infos,'assert!(infos[7].key!=&self.selected);')
elif mode.startswith('repro-constructor'):
 source='use super::*;\n#[kani::proof]\n#[kani::unwind(34)]\n#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFO_KMX::KMX_copy_nonoverlapping)]\n#[kani::stub(<[u8]>::copy_from_slice,crate::NFO_KMX::KMX_copy_from_slice)]\nfn association(){let input:[u8;32]=kani::any();let key=Pubkey::new_from_array(input);let meta=AccountMeta::new_readonly(key,false);'
 if '-byte' in mode:source+='let j:usize=kani::any();kani::assume(j<32);assert!(meta.pubkey.to_bytes()[j]=='+('(input[j]^1)' if mode.endswith('negative') else 'input[j]')+');}'
 else:source+='assert!(meta.pubkey.to_bytes()=='+('{let mut wrong=input;wrong[0]^=1;wrong}' if mode.endswith('negative') else 'input')+');}'
elif mode.startswith('repro-pubkey'):
 source='use super::*;\n#[kani::proof]\n#[kani::unwind(34)]\n#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFO_KMX::KMX_copy_nonoverlapping)]\n#[kani::stub(<[u8]>::copy_from_slice,crate::NFO_KMX::KMX_copy_from_slice)]\nfn association(){let input:[u8;32]=kani::any();let key=Pubkey::new_from_array(input);assert!(key.to_bytes()=='+('{let mut wrong=input;wrong[0]^=1;wrong}' if mode.endswith('negative') else 'input')+');}'
elif mode.startswith('repro-insert'):
 source='use super::*;\nfn insert(input:[u8;32])->[u8;32]{let mut v=Vec::with_capacity(3);v.push(input);v.push([0;32]);v.insert(1,[1;32]);v[0]}\n'
 source+='#[kani::proof]\n#[kani::unwind(34)]\n#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFO_KMX::KMX_copy_nonoverlapping)]\n#[kani::stub(<[u8]>::copy_from_slice,crate::NFO_KMX::KMX_copy_from_slice)]\n'
 source+='fn association(){let input:[u8;32]=kani::any();let j:usize=kani::any();kani::assume(j<32);let out=insert(input);assert!(out[j]=='+('(input[j]^1)' if mode.endswith('negative') else 'input[j]')+');}\n'
elif mode.startswith('repro-growth'):
 source='use super::*;\n'
 source+='fn growth(input:[u8;32])->[u8;32]{let mut v=Vec::with_capacity(1);v.push(input);v.push([0;32]);v[0]}\n'
 source+='#[kani::proof]\n#[kani::unwind(34)]\n#[kani::stub(core::ptr::copy_nonoverlapping,crate::NFO_KMX::KMX_copy_nonoverlapping)]\n#[kani::stub(<[u8]>::copy_from_slice,crate::NFO_KMX::KMX_copy_from_slice)]\n'
 if 'mitigated' in mode:source+='#[kani::stub(alloc::alloc::realloc,crate::NFO_KMX::KMX_realloc)]\n'
 source+='fn association(){let input:[u8;32]=kani::any();let j:usize=kani::any();kani::assume(j<32);let out=growth(input);assert!(out[j]=='+('(input[j]^1)' if mode.endswith('negative') else 'input[j]')+');}\n'
 if '-width-' in mode:
  width=int(mode.split('-width-')[1].split('-')[0]);assert width in [1,2,4,8,16,32];source=source.replace('[u8;32]','[u8;'+str(width)+']').replace('[0;32]','[0;'+str(width)+']').replace('j<32','j<'+str(width))
else:raise SystemExit('unknown isolation')
patch=''
for p in ['programs/aspis-pool/src/pair_forest_dispatch.rs','programs/aspis-pool/src/lib.rs']:
 frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
 hook=frozen+'\n#[cfg(kani)]\n#[path="NFO_read.rs"]\nmod NFO_read;\n' if p.endswith('pair_forest_dispatch.rs') else '#![cfg_attr(kani, feature(allocator_api))]\n'+frozen+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NFO_KMX;\n'
 patch+=''.join(difflib.unified_diff(frozen.splitlines(True),hook.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
p='programs/aspis-pool/src/NFO_read.rs';patch+='--- /dev/null\n+++ b/'+p+'\n@@ -0,0 +1,'+str(len(source.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in source.splitlines())
(E/'NFR_native.patch').write_text(patch);(E/'NFR_CURRENT.json').write_text(json.dumps(dict(mode=mode,source=source,base='NFO_K056',changes='assertion removal only'),indent=1)+'\n')
