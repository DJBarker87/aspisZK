from pathlib import Path
import json,subprocess
B=Path(__file__).parent
p=B/'PoolN_processor_harness.rs'
text=p.read_text().split('\n#[kani::proof]',1)[0].removesuffix('\n}\n')
forest='\n#[cfg(kani)]\nmod PoolN_guards {\nuse super::*;\n'
extra='\n#[cfg(kani)]\nmod PoolN_guards {\nuse super::*;\nuse solana_program::{account_info::AccountInfo,pubkey::Pubkey,program_error::ProgramError};\nuse crate::error::PoolV1ProgramError;\n'
targets=[{'index':1,'harness':'PoolN_ASDI_primary_192','module':'processor','claim':'Complete ASDI: valid80-byte instruction, checkpoint in primary state slot, exact error, no CPI and complete bytes/balance frame.'}]
def add(module,name,n,body,pure=False):
 global text,forest,extra
 owner='&id' if n==192 else '&foreign'
 setup=f'''let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;{n}]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,{owner},false,0);
'''
 block=f'\n#[kani::proof]\n#[kani::unwind({n+4})]\nfn {name}() {{\n'+setup+body+'\ndrop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);\n}\n'
 if module=='processor':text+=block
 elif module=='pair_forest':forest+=block
 else:extra+=block
 targets.append(dict(index=len(targets)+1,harness=name,module=module,claim=body))
add('processor','PoolN_ASDI_primary_1768',1768,'''let mut instruction=[0u8;80]; instruction[..4].copy_from_slice(b"ASDI"); instruction[4]=1; instruction[40]=1;
assert!(decode_deposit_top_level_v1(&instruction).is_ok());
let result=process_deposit_with_runtime_v1(&id,&[account.clone()],&instruction,&mut NoEffects);
assert_eq!(result,Err(ProgramError::IncorrectProgramId));''')
for role in ['core','shard','authority']:
 for n in [192,1768]:
  if role=='core':
   setup='''let mut payer_balance=1; let mut payer_data=[];
let payer_key=Pubkey::new_from_array([9;32]); let system=system_program::id();
let payer=AccountInfo::new(&payer_key,true,true,&mut payer_balance,&mut payer_data,&system,false,0);
let shape=crate::cancel_prepared_settlement_instruction::CancelPreparedSettlementAccountShapeV1::CoreOnly;
let data=encode_cancel_prepared_settlement_instruction_v1(shape);
assert!(decode_cancel_prepared_settlement_instruction_v1(&data).is_ok());
let result=process_cancel_prepared_settlement_with_runtime_v1(&id,&[payer,account.clone()],&data,|_|panic!("unexpected hash"),&mut NoEffects,|_|panic!("unexpected return data"));
assert_eq!(result,Err(ProgramError::InvalidAccountData));'''
  elif role=='shard':
   setup='''let mut payer_balance=1; let mut payer_data=[];let mut core_balance=1;let mut core_data=[0u8;POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES];
let payer_key=Pubkey::new_from_array([9;32]);let core_key=Pubkey::new_from_array([10;32]);let system=system_program::id();
let payer=AccountInfo::new(&payer_key,true,true,&mut payer_balance,&mut payer_data,&system,false,0);
let core=AccountInfo::new(&core_key,false,true,&mut core_balance,&mut core_data,&id,false,0);
assert!(require_prepared_plan_account_v1(&core,&id,POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES).is_ok());
let shape=crate::cancel_prepared_settlement_instruction::CancelPreparedSettlementAccountShapeV1::CoreAndRolloverShard;
let data=encode_cancel_prepared_settlement_instruction_v1(shape);
let result=process_cancel_prepared_settlement_with_runtime_v1(&id,&[payer,core,account.clone()],&data,|_|panic!("unexpected hash"),&mut NoEffects,|_|panic!("unexpected return data"));
assert_eq!(result,Err(ProgramError::InvalidAccountData));'''
  else:
   setup='''let mut core_balance=1;let mut core_data=[];let core_key=Pubkey::new_from_array([9;32]);
let core=AccountInfo::new(&core_key,false,true,&mut core_balance,&mut core_data,&id,false,0);
let shape=crate::cancel_prepared_settlement_instruction::CancelPreparedSettlementAccountShapeV1::CoreOnly;
let data=encode_cancel_prepared_settlement_instruction_v1(shape);
let result=process_cancel_prepared_settlement_with_runtime_v1(&id,&[account.clone(),core],&data,|_|panic!("unexpected hash"),&mut NoEffects,|_|panic!("unexpected return data"));
assert_eq!(result,Err(PoolV1ProgramError::InvalidPayer.into()));'''
  add('processor',f'PoolN_ASPX_{role}_{n}',n,setup)
for kind in ['fresh_roles','postcreate','allocate','withseed','close','plans','payer','token_program']:
 for n in [192,1768]:
  body=''
  if kind=='fresh_roles':
   body='''let sizes=[384usize,768,1000,8256,10000,8504];let i:usize=kani::any();kani::assume(i<sizes.len());
assert_eq!(plan_fresh_program_pda(&account,&id,&key,sizes[i]),Err(PoolV1ProgramError::InvalidFreshAccount.into()));'''
  elif kind=='postcreate':
   body='''let sizes=[384usize,768,1000,8256,10000,8504];let i:usize=kani::any();kani::assume(i<sizes.len());
let prep=if kani::any(){FreshPdaPreparationV1::ProgramOwnedZeroed}else{FreshPdaPreparationV1::CreateOrAllocateSystemOwned};
assert_eq!(require_fresh_rent_exempt_program_pda(&account,&id,&key,sizes[i],prep,&Rent::default()),Err(PoolV1ProgramError::InvalidFreshAccount.into()));'''
  elif kind in ['allocate','withseed','payer']:
   body='''let payer_key=Pubkey::new_from_array([9;32]);let system_key=system_program::id();let loader=native_loader::id();
let mut payer_balance=1;let mut system_balance=1;let mut payer_data=[];let mut system_data=[];
let payer=AccountInfo::new(&payer_key,true,true,&mut payer_balance,&mut payer_data,&system_key,false,0);
let system=AccountInfo::new(&system_key,false,false,&mut system_balance,&mut system_data,&loader,true,0);
assert!(require_payer_and_system_program(&payer,&system).is_ok());
'''
   if kind=='payer':body+='assert_eq!(require_payer_and_system_program(&account,&system),Err(PoolV1ProgramError::InvalidPayer.into()));'
   elif kind=='allocate':body+='assert_eq!(create_or_allocate_pda_with_rent(&mut NoEffects,&payer,&account,&system,192,&id,&[],&Rent::default()),Err(PoolV1ProgramError::InvalidFreshAccount.into()));'
   else:body+='assert_eq!(create_or_allocate_with_seed_with_rent(&mut NoEffects,&payer,&account,&payer,"seed",&system,192,&id,&[],&Rent::default()),Err(PoolV1ProgramError::InvalidFreshAccount.into()));'
  elif kind=='close':
   body='''let refund_key=Pubkey::new_from_array([9;32]);let mut refund_balance:u64=kani::any();let refund_before=refund_balance;let mut refund_data=[];
let refund=AccountInfo::new(&refund_key,true,true,&mut refund_balance,&mut refund_data,&id,false,0);
let size=if kani::any(){POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES}else{POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES};
assert_eq!(close_program_account_v1(&account,&refund,&id,size),Err(ProgramError::InvalidAccountData));
drop(refund);assert!(refund_balance==refund_before);'''
  elif kind=='plans':body='''let size=if kani::any(){POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES}else{POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES};
assert_eq!(require_prepared_plan_account_v1(&account,&id,size),Err(ProgramError::InvalidAccountData));'''
  else:body='assert_eq!(require_token_program_account(&account),Err(PoolV1ProgramError::InvalidTokenProgram.into()));'
  add('processor',f'PoolN_{kind}_{n}',n,body)
for kind in ['master','stored_lane','zero_page','zero_owned']:
 for n in [192,1768]:
  if kind=='master':
   # No private derived type equality or Debug requirement.
   err='PoolV1ProgramError::InvalidAccountType.into()' if n==192 else 'ProgramError::IncorrectProgramId'
   body=f'let result=decode_master_account(&id,&account,true); assert!(matches!(result,Err(e) if e=={err}));'
  elif kind=='stored_lane':body='assert_eq!(stored_lane_bump(&account),Ok(None));'
  elif kind=='zero_page':body='assert_eq!(account_is_zeroed_program_page(&account,&id),Ok(false));'
  else:
   err='PoolV1ProgramError::InvalidFreshAccount.into()' if n==192 else 'ProgramError::IncorrectProgramId'
   body=f'assert_eq!(require_program_owned_zeroed(&account,&id,768,&Rent::default()),Err({err}));'
  add('pair_forest',f'PoolN_{kind}_{n}',n,body)
for kind in ['root_page','marker','token_parsers','lane_codec']:
 for n in [192,1768]:
  if kind=='root_page':body='assert!(matches!(crate::history::validate_root_page_bytes(&account.try_borrow_data().unwrap(),&key,0),Err(e) if e==PoolV1ProgramError::InvalidAccountType.into()));'
  elif kind=='marker':body='assert_eq!(crate::nullifier::recheck_pair_forest_nullifier_marker_v1(&id,&account),Err(PoolV1ProgramError::InvalidNullifierMarkerAccount.into()));'
  elif kind=='token_parsers':body='''let data=account.try_borrow_data().unwrap();
assert!(matches!(crate::vault::parse_legacy_mint_v1(&data),Err(e) if e==PoolV1ProgramError::UnsupportedTokenConfiguration.into()));
assert!(matches!(crate::vault::parse_legacy_token_account_v1(&data),Err(e) if e==PoolV1ProgramError::UnsupportedTokenConfiguration.into()));
drop(data);'''
  else:body='assert!(aspis_statement::pool_v1::decode_pool_v1_pair_forest_lane_state_v1(&account.try_borrow_data().unwrap(),&crate::empty_roots::POOL_V1_PAIR_EMPTY_ROOTS).is_err());'
  add('lib',f'PoolN_{kind}_{n}',n,body)
p.write_text(text+'\n}\n');(B/'PoolN_forest_harness.rs').write_text(forest+'\n}\n');(B/'PoolN_misc_harness.rs').write_text(extra+'\n}\n')
(B/'PoolN_targets.json').write_text(json.dumps(targets,indent=2)+'\n')
assert len(targets)==40,len(targets)
