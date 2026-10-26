from pathlib import Path
B=Path(__file__).parent
out={m:'\n#[cfg(kani)]\nmod PoolN_splits {\nuse super::*;\n' for m in ['processor','pair_forest']}
specs=[('canonical','processor'),('invariant','processor'),('fresh_flags','processor'),('payer_flags','processor'),('master_readonly','pair_forest'),('marker_flags','processor'),('plan_flags','processor')]
for kind,mod in specs:
 for n in [192,1768]:
  fixed=kind in ['canonical','invariant','master_readonly']
  flags=('false,false' if kind=='master_readonly' else 'false,true') if fixed else 'kani::any(),kani::any()'
  block=f'''\n#[kani::proof]\n#[kani::unwind({n+4})]\nfn PoolN_{kind}_{n}() {{
let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let key=Pubkey::new_from_array(kani::any());
let mut bytes:[u8;{n}]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
let account=AccountInfo::new(&key,{flags},&mut balance,&mut bytes,{"&id" if n==192 else "&foreign"},false,0);
'''
  if kind in ['canonical','invariant']:
   expr='load_canonical_pool_state(&id,&account)' if kind=='canonical' else 'CanonicalPoolStateV1::decode_account_from_program_invariant(&id,&account)'
   expected='PoolV1ProgramError::InvalidAccountType.into()' if n==192 else 'ProgramError::IncorrectProgramId'
   block+=f'assert!(matches!({expr},Err(e) if e=={expected}));\n'
  elif kind=='master_readonly':
   expected='PoolV1ProgramError::InvalidAccountType.into()' if n==192 else 'ProgramError::IncorrectProgramId'
   block+=f'assert!(matches!(decode_master_account(&id,&account,false),Err(e) if e=={expected}));\n'
  elif kind=='fresh_flags':
   block+='''let sizes=[384usize,768,1000,8256,10000,8504];let i:usize=kani::any();kani::assume(i<6);
assert_eq!(plan_fresh_program_pda(&account,&id,&key,sizes[i]),Err(PoolV1ProgramError::InvalidFreshAccount.into()));
kani::cover!(account.is_signer && account.is_writable,"signer cannot bypass freshness");
'''
  elif kind=='payer_flags':
   block+='''let system_key=system_program::id();let loader=native_loader::id();let mut sysbal=1;let mut sysdata=[];
let system=AccountInfo::new(&system_key,false,false,&mut sysbal,&mut sysdata,&loader,true,0);
assert_eq!(require_payer_and_system_program(&account,&system),Err(PoolV1ProgramError::InvalidPayer.into()));
kani::cover!(account.is_signer && account.is_writable,"owner rejection reached with signer payer flags");
'''
  elif kind=='marker_flags':block+='assert_eq!(crate::nullifier::recheck_pair_forest_nullifier_marker_v1(&id,&account),Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into()));\n'
  else:block+='''let size=if kani::any(){POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES}else{POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES};
assert_eq!(require_prepared_plan_account_v1(&account,&id,size),Err(ProgramError::InvalidAccountData));
'''
  block+='drop(account);assert!(bytes[0]==before);assert_eq!(balance,initial_balance);\n}\n'
  out[mod]+=block
for mod,src in out.items():(B/f'PoolN_{mod}_splits.rs').write_text(src+'}\n')
