"""Owned scratch-only native cuts; no harness source is printed."""
from pathlib import Path
import sys,json,subprocess,difflib,hashlib,re
E=Path(__file__).resolve().parent;I=E.parent/'pool-b3-20261106'
sys.dont_write_bytecode=True;sys.path.insert(0,str(E))
from NIE_frozen_identity import frozen,apply

def stage(path,source,kind,mode,domain,remaining,extra=None):
 files=dict(frozen());files.update({n:v.encode() for n,v in json.loads((I/'NHP_INCLUDES.json').read_text()).items()})
 apply(files,(I/'NHP_KMX_copy_stubs.patch').read_text())
 original=files[path].decode();after=original+'\n#[cfg(kani)]\nmod NIE_native {\n'+source+'\n}\n'
 root='programs/aspis-pool/src/lib.rs'
 root_before=files[root].decode();root_after='#![cfg_attr(kani, feature(allocator_api))]\n'+root_before+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod KMX_stubs;\n#[cfg(kani)]\npub use KMX_stubs as NIE_KMX;\n'
 root_patch=''.join(difflib.unified_diff(root_before.splitlines(True),root_after.splitlines(True),fromfile='a/'+root,tofile='b/'+root))
 patch=root_patch+''.join(difflib.unified_diff(original.splitlines(True),after.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
 (E/'NIE_native.patch').write_text(patch)
 x=dict(kind=kind,mode=mode,domain=domain,source=source,modifies=[],production_credit=False,remaining=remaining)
 if extra:x.update(extra)
 (E/'NIE_CURRENT.json').write_text(json.dumps(x,indent=2)+'\n')

def attrs():
 return '\n'.join(json.loads((E/'NIE_KMX_ATTRIBUTES.json').read_text())).replace('NHP_KMX','NIE_KMX')

def recheck(case,negative):
 # Each cut differs in admitted caller context: four privilege/owner branches,
 # actual recheck forwarding, optional live shared alias, result and cleanup.
 assert case in range(4)
 setting=['(false,false,true,true)','(true,false,true,true)','(false,true,true,true)','(false,false,false,true)'][case]
 src='''use super::*;
use solana_program::{account_info::AccountInfo,pubkey::Pubkey};
#[kani::proof]
#[kani::unwind(33)]
ATTR
fn association() {
 let mut data: [u8;3] = kani::any();
 let before=data;
 let mut lamports:u64=kani::any();
 let key=Pubkey::new_from_array(kani::any());
 let program=Pubkey::new_from_array(kani::any());
 let owner=solana_sdk_ids::system_program::id();
 kani::assume(program!=owner);
 let len:usize=kani::any();kani::assume(len<=3);
 let (exec,sign,write,system): (bool,bool,bool,bool)=SETTING;
 let account=AccountInfo::new(&key,sign,write,&mut lamports,&mut data[..len],&owner,exec,kani::any());
 let alias=account.clone();
 let shared=if kani::any() {Some(alias.try_borrow_data().unwrap())} else {None};
 let reply=recheck_pair_forest_nullifier_marker_v1(&program,&account);
 let expected_ok= !exec && !sign && write && system && len==0;
 assert!(matches!(reply,Ok(NullifierMarkerPreparationV1::CreateOrAllocateSystemOwned))==expected_ok);
 drop(shared);
 NEGATIVE
 assert!(alias.try_borrow_mut_data().is_ok());
 let query:usize=kani::any();kani::assume(query<len);
 assert!(alias.try_borrow_data().unwrap()[query]==before[query]);
}
'''.replace('ATTR',attrs()).replace('SETTING',setting).replace('NEGATIVE','let leaked=alias.try_borrow_data().unwrap();core::mem::forget(leaked);' if negative else '')
 stage('programs/aspis-pool/src/nullifier.rs',src,'actual recheck -> classifier caller, borrowed alias cleanup case '+str(case),'negative' if negative else 'positive','Canonical AccountInfo on arbitrary 0..3-byte logical backing; arbitrary keys/lamports/rent; System owner distinct from Pool; stated metadata branch; optional live shared alias. No existing exclusive guard.','Full arbitrary production heap/caller prefix and entry/CPI borrow-release association remain OPEN; bounded helper context is not production-domain exclusion of K086.',dict(caller='recheck_pair_forest_nullifier_marker_v1',case=case,control='Leak a shared guard after the actual caller, corrupting borrow-release postcondition' if negative else None))

if __name__=='__main__':recheck(int(sys.argv[1]),sys.argv[2]=='negative')

def decoder(function,case,negative):
 lane='lane' in function
 assert case in (range(5) if lane else range(6))
 # All bodies called here are ACTUAL frozen wrappers or decoders. No callee
 # reply is assumed and no PDA/hash body is reached on these rejection cuts.
 variants=['owner','executable','writable','busy','invalid_lane'] if lane else ['owner','executable','writable','signer','busy','wrong_length']
 branch=variants[case]
 setting={
  'owner':'kani::assume(owner!=program);',
  'executable':'owner=program;exec=true;',
  'writable':'owner=program;exec=false;write='+('false' if lane else 'true')+';',
  'signer':'owner=program;exec=false;write='+('true' if lane else 'false')+';sign=true;',
  'busy':'owner=program;exec=false;write='+('true' if lane else 'false')+';sign=false;',
  'wrong_length':'owner=program;exec=false;write=false;sign=false;',
  'invalid_lane':'owner=program;exec=false;write=true;',
 }[branch]
 expected={'owner':'ProgramError::IncorrectProgramId','executable':'ProgramError::InvalidAccountData','writable':'ProgramError::InvalidAccountData','signer':'ProgramError::InvalidAccountData','busy':'ProgramError::AccountBorrowFailed','wrong_length':'ProgramError::Custom(PoolV1ProgramError::InvalidAccountType as u32)','invalid_lane':'ProgramError::InvalidSeeds'}[branch]
 if function=='decode_master_account':call='decode_master_account(&program,&account,false)'
 elif function=='decode_terminal_master_box_v1':call='decode_terminal_master_box_v1(&program,&account)'
 elif function=='decode_retained_pair_forest_checkpoint_account_v1':call='decode_retained_pair_forest_checkpoint_account_v1(&program,&master,&account)'
 elif function=='decode_terminal_checkpoint_box_v1':call='decode_terminal_checkpoint_box_v1(&program,&master,&account)'
 elif function=='decode_lane_account_from_program_invariant_v1':call='decode_lane_account_from_program_invariant_v1(&program,&master,lane,&account,true)'
 elif function=='decode_terminal_lane_box_v1':call='decode_terminal_lane_box_v1(&program,&master,lane,&account)'
 else:raise ValueError(function)
 src='''use super::*;
use solana_program::{account_info::AccountInfo,pubkey::Pubkey,program_error::ProgramError};
ATTR
#[kani::proof]
#[kani::unwind(33)]
fn association() {
 let mut bytes:[u8;3]=kani::any();let before=bytes;
 let mut balance:u64=kani::any();let old_balance=balance;
 let key=Pubkey::new_from_array(kani::any());let program=Pubkey::new_from_array(kani::any());let master=Pubkey::new_from_array(kani::any());
 let mut owner=Pubkey::new_from_array(kani::any());
 let mut exec:bool=kani::any();let mut sign:bool=kani::any();let mut write:bool=kani::any();
 SETTING
 let len:usize=kani::any();kani::assume(len<=3);
 let lane:u8=kani::any();kani::assume(lane>=8);
 let account=AccountInfo::new(&key,sign,write,&mut balance,&mut bytes[..len],&owner,exec,kani::any());
 let alias=account.clone();
 let exclusive=if BUSY {Some(alias.try_borrow_mut_data().unwrap())} else {None};
 let shared=if !BUSY && kani::any() {Some(alias.try_borrow_data().unwrap())} else {None};
 let result=CALL;
 assert!(matches!(result,Err(ref e) if *e==EXPECTED));
 drop(exclusive);drop(shared);
 NEGATIVE
 assert!(alias.try_borrow_mut_data().is_ok());
 assert!(alias.lamports()==old_balance);
 if len>0 {let q:usize=kani::any();kani::assume(q<len);assert!(alias.try_borrow_data().unwrap()[q]==before[q]);}
 assert!(account.key==&key && account.owner==&owner && account.is_signer==sign && account.is_writable==write && account.executable==exec);
}
'''.replace('ATTR',attrs()).replace('SETTING',setting).replace('BUSY',str(branch=='busy').lower()).replace('CALL',call).replace('EXPECTED',expected).replace('NEGATIVE','let leaked=alias.try_borrow_data().unwrap();core::mem::forget(leaked);' if negative else '')
 stage('programs/aspis-pool/src/pair_forest.rs',src,'actual '+function+' rejected '+branch+' + alias borrow/byte/balance/metadata frame','negative' if negative else 'positive','Valid aliased AccountInfo, arbitrary keys/flags/lamports/rent and logical 0..3 arbitrary bytes; exact '+branch+' source branch. Existing local shared/exclusive guard contexts are explicit; no arbitrary production length premise adopted.','Successful full-image/PDA/arbitrary physical heap and caller-prefix association remain OPEN; this is a new cleanup/frame observation, not reuse of unchanged NHP error-value shapes.',dict(function=function,branch=branch,paired_control='Leak shared guard after the actual rejected prefix'))
