from pathlib import Path
import json,difflib,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent; I=E.parent/"pool-b3-20261106"
sys.path.insert(0,str(E))
from NIZ_frozen_identity import frozen,apply
def stage(path,source,kind,mode,domain,remaining,extra=None):
 files=dict(frozen());files.update({n:v.encode() for n,v in json.loads((I/'NHP_INCLUDES.json').read_text()).items()})
 apply(files,(I/'NHP_KMX_copy_stubs.patch').read_text())
 original=files[path].decode();after=original+'\n#[cfg(kani)]\nmod NIZ_native {\n'+source+'\n}\n'
 root='programs/aspis-pool/src/lib.rs'
 root_before=files[root].decode();root_after='#![cfg_attr(kani, feature(allocator_api))]\n'+root_before+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod KMX_stubs;\n#[cfg(kani)]\npub use KMX_stubs as NIZ_KMX;\n'
 root_patch=''.join(difflib.unified_diff(root_before.splitlines(True),root_after.splitlines(True),fromfile='a/'+root,tofile='b/'+root))
 patch=root_patch+''.join(difflib.unified_diff(original.splitlines(True),after.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
 (E/'NIZ_native.patch').write_text(patch)
 x=dict(kind=kind,mode=mode,domain=domain,source=source,modifies=[],production_credit=False,remaining=remaining)
 if extra:x.update(extra)
 (E/'NIZ_CURRENT.json').write_text(json.dumps(x,indent=2)+'\n')

def attrs():
 return '\n'.join(json.loads((E/'NIZ_KMX_ATTRIBUTES.json').read_text())).replace('NHP_KMX','NIZ_KMX')

def account_setup(n):
 s='use solana_program::{account_info::AccountInfo,pubkey::Pubkey,program_error::ProgramError};\n'
 for i in range(n):
  s+=f'let k{i}=Pubkey::new_from_array(kani::any()); let mut l{i}:u64=kani::any(); let mut d{i}=[kani::any::<u8>()]; let a{i}=AccountInfo::new(&k{i},false,true,&mut l{i},&mut d{i},&k{i},false,0);\n'
 return s

