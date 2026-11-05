"""Generate prefix-owned, local-record splitter observations; never alter release files."""
from pathlib import Path
import json,sys,difflib,hashlib
E=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
sys.path.insert(0,str(E))
from NHP_frozen_identity import frozen,apply
mode=sys.argv[1];kind=sys.argv[2]
assert mode in ['positive','negative'] and kind in ['short','span','storage']
base=dict(frozen());apply(base,(E/'NHP_KMX_copy_stubs.patch').read_text())
if kind=='short':
 source='''use super::*;
#[kani::proof]
#[kani::unwind(8)]
fn association() {
 let input:[u8;3]=kani::any();let n:usize=kani::any();kani::assume(n<4);
 let slice=&input[..n];let before=input;
 let result=split_pair_forest_terminal_bump_hints_v1(slice);
 assert!(matches!(result,Err(ProgramError::InvalidInstructionData)));
 assert!(input==before);
 CONTROL
}
'''
 domain='Every byte array of length 3 and every slice length 0..3; actual frozen splitter; exact error and input frame. No accounts or external effects are reachable.'
else:
 source='''use super::*;
#[kani::proof]
#[kani::unwind(8)]
fn association() {
 let n:usize=kani::any();kani::assume(n>=4&&n<=isize::MAX as usize);
 let layout=core::alloc::Layout::from_size_align(n,1).unwrap();
 let pointer=unsafe { alloc::alloc::alloc_zeroed(layout) };kani::assume(!pointer.is_null());
 let bytes:[u8;4]=kani::any();let split=n-4;
 let i:usize=kani::any();kani::assume(i<=split);
 let byte:u8=kani::any();if i<split {unsafe {pointer.add(i).write(byte);}}
 unsafe {pointer.add(split).write(bytes[0]);pointer.add(split+1).write(bytes[1]);pointer.add(split+2).write(bytes[2]);pointer.add(split+3).write(bytes[3]);}
 {
 let input=unsafe {core::slice::from_raw_parts(pointer,n)};
 let (body,hints)=split_pair_forest_terminal_bump_hints_v1(input).unwrap();
 assert!(body.len()==split);assert!(body.as_ptr()==input.as_ptr());
 assert!(hints.current_page==bytes[0]);assert!(hints.next_page==bytes[1]);
 assert!(hints.vault_authority==bytes[2]);assert!(hints.vault_token_account==bytes[3]);
 if i<split {assert!(body[i]==byte);assert!(input[i]==byte);}
 assert!(input[split]==bytes[0]);assert!(input[split+1]==bytes[1]);assert!(input[split+2]==bytes[2]);assert!(input[split+3]==bytes[3]);
 CONTROL
 }
 unsafe {alloc::alloc::dealloc(pointer,layout);}
}
'''
 domain='Valid returning allocations length 4..isize::MAX; arbitrary four hint bytes, arbitrary selected body offset/value; other body bytes zero. Single selected-cell physical span observation, not arbitrary whole-body credit.'
if kind=='storage':
 source=source.replace(' let (body,hints)=split_pair_forest_terminal_bump_hints_v1(input).unwrap();','').replace(' assert!(body.len()==split);assert!(body.as_ptr()==input.as_ptr());','')
 source='\n'.join(l for l in source.split('\n') if 'hints.' not in l).replace('assert!(body[i]==byte);','')
 domain='Pre-call dynamic allocation storage isolation, same unrestricted lengths as K003; splitter not reached. No production credit.'
control=''
if mode=='negative':
 if kind=='short':source=source.replace('matches!(result,Err(ProgramError::InvalidInstructionData))','matches!(result,Err(ProgramError::InvalidAccountData))')
 else:source=source.replace('hints.current_page==bytes[0]','hints.current_page==(bytes[0]^1)')
source=source.replace('CONTROL',control)
path='programs/aspis-pool/src/pair_forest.rs'
new=base[path].decode()+'\n#[cfg(kani)]\nmod NHP_dispatch {\n'+source+'}\n'
patch=''.join(difflib.unified_diff(base[path].decode().splitlines(True),new.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
(E/'NHP_native.patch').write_text(patch)
(E/'NHP_CURRENT.json').write_text(json.dumps(dict(kind='dispatch splitter '+kind,mode=mode,source=source,domain=domain,modifies=['local records','private allocation only' if kind=='span' else 'none'],production_credit=False,remaining='processor/guard/discriminator and caller physical association; span family additionally arbitrary-tail frame'),indent=1)+'\n')
print(json.dumps(dict(kind=kind,mode=mode,patch_sha256=hashlib.sha256(patch.encode()).hexdigest(),source_suppressed=True)))
