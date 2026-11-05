"""Actual locked SDK From<u64>, scalar constructor projection and one String window."""
from pathlib import Path
import re,json,sys,subprocess,difflib,hashlib
E=Path(__file__).resolve().parent;mode=sys.argv[1];assert mode in ['positive','negative','borsh_negative']
sdk=(E/'NHP_pinned_inputs/NHP_solana_program_error_222.rs').read_text();instruction=(E/'NHP_pinned_inputs/NHP_solana_instruction_233_error.rs').read_text()
constants={n:int(i)<<32 for n,i in re.findall(r'pub const (\w+): u64\s*=\s*to_builtin!\((\d+)\)',instruction)}
body=sdk.split('pub enum ProgramError {',1)[1].split('\n}',1)[0];variants=re.findall(r'^    (\w+)(?:\([^\n]*\))?,',body,re.M);assert len(variants)==26
conversion=sdk.split('impl From<u64> for ProgramError {',1)[1].split('\n}',1)[0]
rows=[]
for constant,variant in re.findall(r'([A-Z_]+)\s*=>\s*(?:\{\s*)?Self::(\w+)',conversion):
 if constant=='_':continue
 assert constant in constants and variant in variants
 rows.append(dict(constant=constant,word=constants[constant],variant=variant,tag=variants.index(variant)))
assert len(rows)==26 and len({r['word'] for r in rows})==26
reference='pub fn classify(word:u64)->(u8,u32) {\n match word {\n'+''.join(f" {r['word']}u64 => ({r['tag']}u8,0u32),\n" for r in rows)+' _ => (0u8,word as u32),\n }\n}\n'
actual=''
for tag,v in enumerate(variants):
 if v=='Custom':actual+='ProgramError::Custom(value)=>(0u8,value),\n'
 elif v=='BorshIoError':
  predicate='bytes[index]==b"Unknown"[index]' if mode!='borsh_negative' else 'bytes[index]==(b"Unknown"[index]^1)'
  actual+=f'ProgramError::BorshIoError(text)=>{{let bytes=text.as_bytes();assert!(bytes.len()==7);let index:usize=kani::any();kani::assume(index<7);assert!({predicate});({tag}u8,0u32)}},\n'
 else:actual+=f'ProgramError::{v}=>({tag}u8,0u32),\n'
source='''use super::*;
#[kani::proof]
#[kani::unwind(33)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NHP_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NHP_KMX::KMX_copy_from_slice)]
#[kani::stub(alloc::alloc::realloc,crate::NHP_KMX::KMX_realloc)]
fn association(){
 let word:u64=kani::any();
 PRE
 let returned=ProgramError::from(word);
 let observed=match returned { ARMS };
 let mut expected=crate::NHP_error_reference::classify(word);
 CONTROL
 assert!(observed==expected);
}
'''.replace('ARMS',actual).replace('PRE',f"kani::assume(word=={constants['BORSH_IO_ERROR']}u64);" if mode=='borsh_negative' else '').replace('CONTROL','expected.0^=1;' if mode=='negative' else '')
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';read=lambda p:subprocess.check_output(['git','show',rev+':'+p],text=True)
patch=''
for path in ['programs/aspis-pool/src/error.rs','programs/aspis-pool/src/lib.rs']:
 before=read(path)
 if path.endswith('/error.rs'):after=before+'\n#[cfg(kani)]\nmod NHP_ErrorWord {\n'+source+'}\n'
 else:after='#![cfg_attr(kani, feature(allocator_api))]\n'+before+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NHP_KMX;\n#[cfg(any(kani,NHP_extract))]\npub mod NHP_error_reference;\n'
 patch+=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
path='programs/aspis-pool/src/NHP_error_reference.rs';patch+='--- /dev/null\n+++ b/'+path+'\n@@ -0,0 +1,'+str(len(reference.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in reference.splitlines())
(E/'NHP_native.patch').write_text(patch);(E/'NHP_error_reference.rs').write_text(reference)
(E/'NHP_WORD_MAPPING.json').write_text(json.dumps(dict(constructors=rows,unknown_utf8=list(b'Unknown'),reference_sha256=hashlib.sha256(reference.encode()).hexdigest(),sdk_sha256=hashlib.sha256(sdk.encode()).hexdigest(),instruction_sha256=hashlib.sha256(instruction.encode()).hexdigest()),indent=2)+'\n')
(E/'NHP_CURRENT.json').write_text(json.dumps(dict(kind='SDK From u64 constructor and Borsh window',mode=mode,source=source,reference=reference,domain='Every u64 word; arbitrary selected String byte index0..6 in BorshIoError branch; dedicated String corruption control narrows to that branch',modifies=['fresh owned String allocation for Borsh variant only'],production_credit=False,remaining='coherent op44 model association and complete owned String/allocator/caller frame; no universal arbitrary String claim'),indent=1)+'\n')
print('error::NHP_ErrorWord::association')
