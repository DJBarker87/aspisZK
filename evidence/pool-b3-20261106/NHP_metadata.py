"""Prefix-owned metadata and decoder rejection cuts. Generated source is never printed."""
from pathlib import Path
import json,sys,difflib,subprocess,hashlib
E=Path(__file__).resolve().parent;mode,kind=sys.argv[1:];assert mode in ['positive','negative']
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';read=lambda p:subprocess.check_output(['git','show',rev+':'+p],text=True)
reference=(E.parent/'pool-prefix-20261105/NGG_E001/NGG_reference.rs').read_text()
parts=kind.split('-');target=parts[0];case='-'.join(parts[1:])
module='pair_forest_dispatch' if target in ['verifier','transport'] else 'processor' if target in ['payer','token'] else 'pair_forest'
head='use super::*;\nmod model {\n'+reference+'\n}\n'
attrs='''#[kani::proof]
#[kani::unwind(33)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NHP_KMX::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::NHP_KMX::KMX_copy_from_slice)]
#[kani::stub(alloc::alloc::realloc,crate::NHP_KMX::KMX_realloc)]
fn association(){
'''
setup=''
for j in range(3):
 setup+=f'''let k{j}=Pubkey::new_from_array(kani::any());let o{j}=Pubkey::new_from_array(kani::any());
let mut l{j}:u64=kani::any();let mut d{j}:[u8;3]=kani::any();
let s{j}:bool=kani::any();let w{j}:bool=kani::any();let e{j}:bool=kani::any();
let mut a{j}=AccountInfo::new(&k{j},s{j},w{j},&mut l{j},&mut d{j},&o{j},e{j},kani::any());
let m{j}=model::Account{{key:k{j}.to_bytes(),owner:o{j}.to_bytes(),signer:s{j},writable:w{j},executable:e{j}}};
let before{j}=(**a{j}.lamports.borrow(),a{j}.data.borrow().to_vec());
'''
setup+='let p=Pubkey::new_from_array(kani::any());let selected=Pubkey::new_from_array(kani::any());let lane:u8=kani::any();\n'
if case=='alias':
 setup+='a1.data=a0.data.clone();a1.lamports=a0.lamports.clone();a2.data=a0.data.clone();a2.lamports=a0.lamports.clone();\n'
 for j in [1,2]:setup+=f'let before{j}=(**a{j}.lamports.borrow(),a{j}.data.borrow().to_vec());\n'

maperr='''let expected=r.map_err(|err|match err {
model::Error::InvalidVerifierProgram=>crate::error::PoolV1ProgramError::InvalidVerifierProgramAccount.into(),
model::Error::NotEnoughAccountKeys=>ProgramError::NotEnoughAccountKeys,
model::Error::InvalidVerifierProof=>crate::error::PoolV1ProgramError::InvalidVerifierProofAccount.into(),
model::Error::InvalidPayer=>crate::error::PoolV1ProgramError::InvalidPayer.into(),
model::Error::InvalidSystemProgram=>crate::error::PoolV1ProgramError::InvalidSystemProgram.into(),
model::Error::InvalidTokenProgram=>crate::error::PoolV1ProgramError::InvalidTokenProgram.into(),
model::Error::InvalidArgument=>ProgramError::InvalidArgument,
});
'''
loaders='[solana_sdk_ids::bpf_loader::id().to_bytes(),solana_sdk_ids::bpf_loader_upgradeable::id().to_bytes(),solana_sdk_ids::loader_v4::id().to_bytes()]'
if target=='verifier':
 body=f'let r=model::verifier(&m0,&selected.to_bytes(),&{loaders});\nlet actual=super::require_verifier_program(&a0,&selected);\n'+maperr
elif target=='token':
 body=f'let r=model::token(&m0,&crate::vault::LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes(),&{loaders});\nlet actual=super::require_token_program_account(&a0);\n'+maperr
elif target=='payer':
 body='let r=model::payer(&m0,&m1,&solana_sdk_ids::system_program::id().to_bytes(),&solana_sdk_ids::native_loader::id().to_bytes());\nlet actual=super::require_payer_and_system_program(&a0,&a1);\n'+maperr
elif target=='transport':
 body='let present:bool=kani::any();let r=model::transport(&m0,&m1,if present {Some(&m2)}else{None});\nlet actual=super::proof_transport_verifier(&a0,&a1,if present {Some(&a2)}else{None}).map(|k|k.to_bytes());\n'+maperr
else:
 assert target in ['master','checkpoint','lane']
 writable='true' if target=='lane' else 'false'
 metadata=f'o0!=p||e0||w0!={writable}'
 if case=='metadata':
  setup+=f'kani::assume({metadata});\n'
  expectation=f'if o0!=p {{ProgramError::IncorrectProgramId}} else {{ProgramError::InvalidAccountData}}'
 elif case in ['ownerbusy','flagsbusy','signerbusy','ownershared','shared','invalidlane']:
  if case in ['ownerbusy','ownershared']:
   setup+='kani::assume(o0!=p);\n';expectation='ProgramError::IncorrectProgramId'
  elif case=='flagsbusy':
   setup+=f'kani::assume(o0==p&&(e0||w0!={writable}));\n';expectation='ProgramError::InvalidAccountData'
  elif case=='signerbusy':
   assert target!='lane';setup+='kani::assume(o0==p&&!e0&&!w0&&s0);\n';expectation='ProgramError::InvalidAccountData'
  elif case=='shared':
   assert target!='lane';setup+='kani::assume(o0==p&&!e0&&!w0&&!s0);\n';expectation='crate::error::PoolV1ProgramError::InvalidAccountType.into()'
  else:
   assert target=='lane';setup+='kani::assume(o0==p&&!e0&&w0&&lane>=8);\n';expectation='ProgramError::InvalidSeeds'
  if case in ['ownershared','shared','invalidlane']:setup+='let held=a0.try_borrow_data().unwrap();\n'
  else:setup+='let held=a0.try_borrow_mut_data().unwrap();let held_lamports=a0.try_borrow_mut_lamports().unwrap();\n'
 elif case=='signer':
  assert target!='lane';setup+='kani::assume(o0==p&&!e0&&!w0&&s0);\n';expectation='ProgramError::InvalidAccountData'
 elif case=='borrow':
  setup+=f'kani::assume(o0==p&&!e0&&w0=={writable}'+('&&!s0' if target!='lane' else '')+');\nlet held=a0.try_borrow_mut_data().unwrap();\n'
  expectation='ProgramError::AccountBorrowFailed'
 elif case=='length':
  assert target!='lane';setup+='kani::assume(o0==p&&!e0&&!w0&&!s0);\n';expectation='crate::error::PoolV1ProgramError::InvalidAccountType.into()'
 else:raise AssertionError(case)
 call={'master':'super::decode_terminal_master_box_v1(&p,&a0)','checkpoint':'super::decode_terminal_checkpoint_box_v1(&p,&selected,&a0)','lane':'super::decode_terminal_lane_box_v1(&p,&selected,lane,&a0)'}[target]
 body=f'let expected:ProgramError={expectation};\nlet actual={call}.err();\n'
 if case in ['borrow','ownerbusy','flagsbusy','signerbusy','ownershared','shared','invalidlane']:
  body+='assert!(held.len()==3);drop(held);\n'
  if case in ['ownerbusy','flagsbusy','signerbusy']:body+='assert!(**held_lamports==before0.0);drop(held_lamports);\n'
  body+='assert!(a0.try_borrow_mut_data().is_ok());assert!(a0.try_borrow_mut_lamports().is_ok());\n'
 if mode=='negative':body+='assert!(actual==Some(ProgramError::InvalidArgument));\n'
 else:body+='assert!(actual==Some(expected));\n'
if target in ['verifier','token','payer','transport']:
 if mode=='negative':body+='assert!(actual!=expected);\n'
 else:body+='assert!(actual==expected);\n'
frame=''
for j in range(3):
 frame+=f'assert!(**a{j}.lamports.borrow()==before{j}.0);assert!(*a{j}.data.borrow()==before{j}.1.as_slice());assert!(a{j}.key==&k{j}&&a{j}.owner==&o{j}&&a{j}.is_signer==s{j}&&a{j}.is_writable==w{j}&&a{j}.executable==e{j});\n'
source=head+attrs+setup+body+frame+'}\n'
patch=''
for p in ['programs/aspis-pool/src/'+module+'.rs','programs/aspis-pool/src/lib.rs']:
 f=read(p)
 after=f+'\n#[cfg(kani)]\nmod NHP_metadata {\n'+source+'}\n' if not p.endswith('/lib.rs') else '#![cfg_attr(kani, feature(allocator_api))]\n'+f+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NHP_KMX;\n'
 patch+=''.join(difflib.unified_diff(f.splitlines(True),after.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
(E/'NHP_native.patch').write_text(patch)
(E/'NHP_CURRENT.json').write_text(json.dumps(dict(kind=kind,mode=mode,source=source,domain='Arbitrary metadata, keys, lamports and 3-byte payloads of valid independently allocated AccountInfo; case restrictions explicitly in source; no production length premise adopted',modifies=[],production_credit=False,remaining='Arbitrary physical data/lamports cell and alias/borrow domain; caller packet association; decoded happy-path/PDA packets',reference='evidence/pool-prefix-20261105/NGG_E001/NGG_reference.rs',reference_sha256=hashlib.sha256(reference.encode()).hexdigest()),indent=1)+'\n')
print(module+'::NHP_metadata::association')
