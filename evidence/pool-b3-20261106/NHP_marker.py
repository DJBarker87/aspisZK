"""Actual marker classifier branches before its zero scan; no SHA or CPI model."""
from pathlib import Path
import subprocess,json,sys,difflib
E=Path(__file__).resolve().parent;mode,case=sys.argv[1:];assert mode in ['positive','negative']
assert case in ['privileges','privilegesbusy','programborrow','programlength','systemempty','systemshared','systemnonempty','foreignbusy','systembusy']
setup='''use super::*;
#[kani::proof]
#[kani::unwind(33)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NHP_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NHP_KMX::KMX_copy_from_slice)]
#[kani::stub(alloc::alloc::realloc,crate::NHP_KMX::KMX_realloc)]
fn association(){
 let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let program=Pubkey::new_from_array(kani::any());
 let signer:bool=kani::any();let writable:bool=kani::any();let executable:bool=kani::any();let mut lamports:u64=kani::any();let mut data:[u8;3]=kani::any();
 let n:usize=LENGTH;
 let a=AccountInfo::new(&key,signer,writable,&mut lamports,&mut data[..n],&owner,executable,kani::any());
 let before=(**a.lamports.borrow(),a.data.borrow().to_vec());
'''.replace('LENGTH','0' if case in ['systemempty','systemshared','systembusy'] else '3')
if case.startswith('privileges'):setup+='kani::assume(executable||signer||!writable);\n'
else:setup+='kani::assume(!executable&&!signer&&writable);\n'
if case.startswith('program'):setup+='kani::assume(owner==program);\n'
elif case.startswith('system'):setup+='kani::assume(owner==system_program::id()&&program!=system_program::id());\n'
elif case=='foreignbusy':setup+='kani::assume(owner!=program&&owner!=system_program::id());\n'
exclusive=case in ['privilegesbusy','programborrow','foreignbusy','systembusy'];shared=case in ['systemshared','systemnonempty']
if exclusive:setup+='let held=a.try_borrow_mut_data().unwrap();let held_lamports=a.try_borrow_mut_lamports().unwrap();\n'
elif shared:setup+='let held=a.try_borrow_data().unwrap();\n'
expected=(0,0) if case in ['systemempty','systemshared'] else (3,0) if case in ['programborrow','systembusy'] else (2,0x41532025)
body='''let result=super::classify_nullifier_marker_account_v1(&program,&a);
let code:(u8,u64)=match result {
 Ok(NullifierMarkerPreparationV1::CreateOrAllocateSystemOwned)=>(0,0),
 Ok(NullifierMarkerPreparationV1::PopulateProgramOwnedZeroed)=>(1,0),
 Err(ProgramError::Custom(value))=>(2,u64::from(value)),
 Err(ProgramError::AccountBorrowFailed)=>(3,0),
 _=>(4,0),
};
'''
if exclusive or shared:body+='assert!(held.len()==n);drop(held);\n'
if exclusive:body+='assert!(**held_lamports==before.0);drop(held_lamports);\n'
body+=f'assert!(code==({expected[0] ^ (1 if mode=="negative" else 0)}u8,{expected[1]}u64));\n'
body+='''assert!(**a.lamports.borrow()==before.0);assert!(*a.data.borrow()==before.1.as_slice());
assert!(a.key==&key&&a.owner==&owner&&a.is_signer==signer&&a.is_writable==writable&&a.executable==executable);
assert!(a.try_borrow_mut_data().is_ok());assert!(a.try_borrow_mut_lamports().is_ok());
}
'''
source=setup+body
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';read=lambda p:subprocess.check_output(['git','show',rev+':'+p],text=True);patch=''
for p in ['programs/aspis-pool/src/nullifier.rs','programs/aspis-pool/src/lib.rs']:
 before=read(p)
 after=before+'\n#[cfg(kani)]\nmod NHP_marker {\n'+source+'}\n' if p.endswith('/nullifier.rs') else '#![cfg_attr(kani, feature(allocator_api))]\n'+before+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NHP_KMX;\n'
 patch+=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
(E/'NHP_native.patch').write_text(patch);(E/'NHP_CURRENT.json').write_text(json.dumps(dict(kind='marker '+case,mode=mode,source=source,domain='Arbitrary metadata and three-byte backing; empty or3-byte logical view, with stated source branch and existing live-guard class',modifies=[],production_credit=False,remaining='arbitrary physical marker image/borrow domain, address/hash logs, zero-loop association, plan/create/recheck CPI frames; systembusy is a proposed-error counterexample probe'),indent=1)+'\n')
print('nullifier::NHP_marker::association')
