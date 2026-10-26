
#[cfg(kani)]
mod PoolN_guards {
    use super::*;
    struct NoEffects;
    impl PoolCpiRuntimeV1 for NoEffects {
        fn invoke<'a>(&mut self, _: &Instruction, _: &[AccountInfo<'a>]) -> ProgramResult {
            panic!("unexpected CPI")
        }
        fn invoke_signed<'a>(&mut self, _: &Instruction, _: &[AccountInfo<'a>], _: &[&[&[u8]]]) -> ProgramResult {
            panic!("unexpected signed CPI")
        }
        fn close_program_account<'a>(&mut self, _: &AccountInfo<'a>, _: &AccountInfo<'a>, _: &Pubkey, _: usize) -> ProgramResult {
            panic!("unexpected close")
        }
    }
    #[kani::proof]
    #[kani::unwind(195)]
    fn PoolN_ASDI_primary_192() {
        let id = Pubkey::new_from_array([7;32]);
        let key = Pubkey::new_from_array([8;32]);
        let mut bytes: [u8;192] = kani::any();
        let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
        let mut balance: u64 = kani::any();
        let initial_balance=balance;
        let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&id,false,0);
        let mut instruction=[0u8;80];
        instruction[..4].copy_from_slice(b"ASDI"); instruction[4]=1; instruction[40]=1;
        assert!(decode_deposit_top_level_v1(&instruction).is_ok());
        let result=process_deposit_with_runtime_v1(&id,&[account.clone()],&instruction,&mut NoEffects);
        assert_eq!(result, Err(PoolV1ProgramError::InvalidAccountType.into()));
        drop(account); assert!(bytes[probe]==before); assert!(balance==initial_balance);
    }
#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_ASDI_primary_1768() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;1768]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&foreign,false,0);
let mut instruction=[0u8;80]; instruction[..4].copy_from_slice(b"ASDI"); instruction[4]=1; instruction[40]=1;
assert!(decode_deposit_top_level_v1(&instruction).is_ok());
let result=process_deposit_with_runtime_v1(&id,&[account.clone()],&instruction,&mut NoEffects);
assert_eq!(result,Err(ProgramError::IncorrectProgramId));
drop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_ASPX_core_192() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;192]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&id,false,0);
let mut payer_balance=1; let mut payer_data=[];
let payer_key=Pubkey::new_from_array([9;32]); let system=system_program::id();
let payer=AccountInfo::new(&payer_key,true,true,&mut payer_balance,&mut payer_data,&system,false,0);
let shape=crate::cancel_prepared_settlement_instruction::CancelPreparedSettlementAccountShapeV1::CoreOnly;
let data=encode_cancel_prepared_settlement_instruction_v1(shape);
assert!(decode_cancel_prepared_settlement_instruction_v1(&data).is_ok());
let result=process_cancel_prepared_settlement_with_runtime_v1(&id,&[payer,account.clone()],&data,|_|panic!("unexpected hash"),&mut NoEffects,|_|panic!("unexpected return data"));
assert_eq!(result,Err(ProgramError::InvalidAccountData));
drop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_ASPX_core_1768() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;1768]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&foreign,false,0);
let mut payer_balance=1; let mut payer_data=[];
let payer_key=Pubkey::new_from_array([9;32]); let system=system_program::id();
let payer=AccountInfo::new(&payer_key,true,true,&mut payer_balance,&mut payer_data,&system,false,0);
let shape=crate::cancel_prepared_settlement_instruction::CancelPreparedSettlementAccountShapeV1::CoreOnly;
let data=encode_cancel_prepared_settlement_instruction_v1(shape);
assert!(decode_cancel_prepared_settlement_instruction_v1(&data).is_ok());
let result=process_cancel_prepared_settlement_with_runtime_v1(&id,&[payer,account.clone()],&data,|_|panic!("unexpected hash"),&mut NoEffects,|_|panic!("unexpected return data"));
assert_eq!(result,Err(ProgramError::InvalidAccountData));
drop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_ASPX_shard_192() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;192]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&id,false,0);
let mut payer_balance=1; let mut payer_data=[];let mut core_balance=1;let mut core_data=[0u8;POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES];
let payer_key=Pubkey::new_from_array([9;32]);let core_key=Pubkey::new_from_array([10;32]);let system=system_program::id();
let payer=AccountInfo::new(&payer_key,true,true,&mut payer_balance,&mut payer_data,&system,false,0);
let core=AccountInfo::new(&core_key,false,true,&mut core_balance,&mut core_data,&id,false,0);
assert!(require_prepared_plan_account_v1(&core,&id,POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES).is_ok());
let shape=crate::cancel_prepared_settlement_instruction::CancelPreparedSettlementAccountShapeV1::CoreAndRolloverShard;
let data=encode_cancel_prepared_settlement_instruction_v1(shape);
let result=process_cancel_prepared_settlement_with_runtime_v1(&id,&[payer,core,account.clone()],&data,|_|panic!("unexpected hash"),&mut NoEffects,|_|panic!("unexpected return data"));
assert_eq!(result,Err(ProgramError::InvalidAccountData));
drop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_ASPX_shard_1768() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;1768]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&foreign,false,0);
let mut payer_balance=1; let mut payer_data=[];let mut core_balance=1;let mut core_data=[0u8;POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES];
let payer_key=Pubkey::new_from_array([9;32]);let core_key=Pubkey::new_from_array([10;32]);let system=system_program::id();
let payer=AccountInfo::new(&payer_key,true,true,&mut payer_balance,&mut payer_data,&system,false,0);
let core=AccountInfo::new(&core_key,false,true,&mut core_balance,&mut core_data,&id,false,0);
assert!(require_prepared_plan_account_v1(&core,&id,POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES).is_ok());
let shape=crate::cancel_prepared_settlement_instruction::CancelPreparedSettlementAccountShapeV1::CoreAndRolloverShard;
let data=encode_cancel_prepared_settlement_instruction_v1(shape);
let result=process_cancel_prepared_settlement_with_runtime_v1(&id,&[payer,core,account.clone()],&data,|_|panic!("unexpected hash"),&mut NoEffects,|_|panic!("unexpected return data"));
assert_eq!(result,Err(ProgramError::InvalidAccountData));
drop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_ASPX_authority_192() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;192]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&id,false,0);
let mut core_balance=1;let mut core_data=[];let core_key=Pubkey::new_from_array([9;32]);
let core=AccountInfo::new(&core_key,false,true,&mut core_balance,&mut core_data,&id,false,0);
let shape=crate::cancel_prepared_settlement_instruction::CancelPreparedSettlementAccountShapeV1::CoreOnly;
let data=encode_cancel_prepared_settlement_instruction_v1(shape);
let result=process_cancel_prepared_settlement_with_runtime_v1(&id,&[account.clone(),core],&data,|_|panic!("unexpected hash"),&mut NoEffects,|_|panic!("unexpected return data"));
assert_eq!(result,Err(PoolV1ProgramError::InvalidPayer.into()));
drop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_ASPX_authority_1768() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;1768]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&foreign,false,0);
let mut core_balance=1;let mut core_data=[];let core_key=Pubkey::new_from_array([9;32]);
let core=AccountInfo::new(&core_key,false,true,&mut core_balance,&mut core_data,&id,false,0);
let shape=crate::cancel_prepared_settlement_instruction::CancelPreparedSettlementAccountShapeV1::CoreOnly;
let data=encode_cancel_prepared_settlement_instruction_v1(shape);
let result=process_cancel_prepared_settlement_with_runtime_v1(&id,&[account.clone(),core],&data,|_|panic!("unexpected hash"),&mut NoEffects,|_|panic!("unexpected return data"));
assert_eq!(result,Err(PoolV1ProgramError::InvalidPayer.into()));
drop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_fresh_roles_192() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;192]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&id,false,0);
let sizes=[384usize,768,1000,8256,10000,8504];let i:usize=kani::any();kani::assume(i<sizes.len());
assert_eq!(plan_fresh_program_pda(&account,&id,&key,sizes[i]),Err(PoolV1ProgramError::InvalidFreshAccount.into()));
drop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_fresh_roles_1768() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;1768]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&foreign,false,0);
let sizes=[384usize,768,1000,8256,10000,8504];let i:usize=kani::any();kani::assume(i<sizes.len());
assert_eq!(plan_fresh_program_pda(&account,&id,&key,sizes[i]),Err(PoolV1ProgramError::InvalidFreshAccount.into()));
drop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_postcreate_192() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;192]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&id,false,0);
let sizes=[384usize,768,1000,8256,10000,8504];let i:usize=kani::any();kani::assume(i<sizes.len());
let prep=if kani::any(){FreshPdaPreparationV1::ProgramOwnedZeroed}else{FreshPdaPreparationV1::CreateOrAllocateSystemOwned};
assert_eq!(require_fresh_rent_exempt_program_pda(&account,&id,&key,sizes[i],prep,&Rent::default()),Err(PoolV1ProgramError::InvalidFreshAccount.into()));
drop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_postcreate_1768() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;1768]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&foreign,false,0);
let sizes=[384usize,768,1000,8256,10000,8504];let i:usize=kani::any();kani::assume(i<sizes.len());
let prep=if kani::any(){FreshPdaPreparationV1::ProgramOwnedZeroed}else{FreshPdaPreparationV1::CreateOrAllocateSystemOwned};
assert_eq!(require_fresh_rent_exempt_program_pda(&account,&id,&key,sizes[i],prep,&Rent::default()),Err(PoolV1ProgramError::InvalidFreshAccount.into()));
drop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_allocate_192() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;192]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&id,false,0);
let payer_key=Pubkey::new_from_array([9;32]);let system_key=system_program::id();let loader=native_loader::id();
let mut payer_balance=1;let mut system_balance=1;let mut payer_data=[];let mut system_data=[];
let payer=AccountInfo::new(&payer_key,true,true,&mut payer_balance,&mut payer_data,&system_key,false,0);
let system=AccountInfo::new(&system_key,false,false,&mut system_balance,&mut system_data,&loader,true,0);
assert!(require_payer_and_system_program(&payer,&system).is_ok());
assert_eq!(create_or_allocate_pda_with_rent(&mut NoEffects,&payer,&account,&system,192,&id,&[],&Rent::default()),Err(PoolV1ProgramError::InvalidFreshAccount.into()));
drop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_allocate_1768() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;1768]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&foreign,false,0);
let payer_key=Pubkey::new_from_array([9;32]);let system_key=system_program::id();let loader=native_loader::id();
let mut payer_balance=1;let mut system_balance=1;let mut payer_data=[];let mut system_data=[];
let payer=AccountInfo::new(&payer_key,true,true,&mut payer_balance,&mut payer_data,&system_key,false,0);
let system=AccountInfo::new(&system_key,false,false,&mut system_balance,&mut system_data,&loader,true,0);
assert!(require_payer_and_system_program(&payer,&system).is_ok());
assert_eq!(create_or_allocate_pda_with_rent(&mut NoEffects,&payer,&account,&system,192,&id,&[],&Rent::default()),Err(PoolV1ProgramError::InvalidFreshAccount.into()));
drop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_withseed_192() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;192]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&id,false,0);
let payer_key=Pubkey::new_from_array([9;32]);let system_key=system_program::id();let loader=native_loader::id();
let mut payer_balance=1;let mut system_balance=1;let mut payer_data=[];let mut system_data=[];
let payer=AccountInfo::new(&payer_key,true,true,&mut payer_balance,&mut payer_data,&system_key,false,0);
let system=AccountInfo::new(&system_key,false,false,&mut system_balance,&mut system_data,&loader,true,0);
assert!(require_payer_and_system_program(&payer,&system).is_ok());
assert_eq!(create_or_allocate_with_seed_with_rent(&mut NoEffects,&payer,&account,&payer,"seed",&system,192,&id,&[],&Rent::default()),Err(PoolV1ProgramError::InvalidFreshAccount.into()));
drop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_withseed_1768() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;1768]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&foreign,false,0);
let payer_key=Pubkey::new_from_array([9;32]);let system_key=system_program::id();let loader=native_loader::id();
let mut payer_balance=1;let mut system_balance=1;let mut payer_data=[];let mut system_data=[];
let payer=AccountInfo::new(&payer_key,true,true,&mut payer_balance,&mut payer_data,&system_key,false,0);
let system=AccountInfo::new(&system_key,false,false,&mut system_balance,&mut system_data,&loader,true,0);
assert!(require_payer_and_system_program(&payer,&system).is_ok());
assert_eq!(create_or_allocate_with_seed_with_rent(&mut NoEffects,&payer,&account,&payer,"seed",&system,192,&id,&[],&Rent::default()),Err(PoolV1ProgramError::InvalidFreshAccount.into()));
drop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_close_192() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;192]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&id,false,0);
let refund_key=Pubkey::new_from_array([9;32]);let mut refund_balance:u64=kani::any();let refund_before=refund_balance;let mut refund_data=[];
let refund=AccountInfo::new(&refund_key,true,true,&mut refund_balance,&mut refund_data,&id,false,0);
let size=if kani::any(){POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES}else{POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES};
assert_eq!(close_program_account_v1(&account,&refund,&id,size),Err(ProgramError::InvalidAccountData));
drop(refund);assert!(refund_balance==refund_before);
drop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_close_1768() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;1768]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&foreign,false,0);
let refund_key=Pubkey::new_from_array([9;32]);let mut refund_balance:u64=kani::any();let refund_before=refund_balance;let mut refund_data=[];
let refund=AccountInfo::new(&refund_key,true,true,&mut refund_balance,&mut refund_data,&id,false,0);
let size=if kani::any(){POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES}else{POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES};
assert_eq!(close_program_account_v1(&account,&refund,&id,size),Err(ProgramError::InvalidAccountData));
drop(refund);assert!(refund_balance==refund_before);
drop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_plans_192() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;192]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&id,false,0);
let size=if kani::any(){POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES}else{POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES};
assert_eq!(require_prepared_plan_account_v1(&account,&id,size),Err(ProgramError::InvalidAccountData));
drop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_plans_1768() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;1768]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&foreign,false,0);
let size=if kani::any(){POOL_V1_PREPARED_SETTLEMENT_CORE_ACCOUNT_BYTES}else{POOL_V1_PREPARED_SETTLEMENT_ROLLOVER_ACCOUNT_BYTES};
assert_eq!(require_prepared_plan_account_v1(&account,&id,size),Err(ProgramError::InvalidAccountData));
drop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_payer_192() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;192]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&id,false,0);
let payer_key=Pubkey::new_from_array([9;32]);let system_key=system_program::id();let loader=native_loader::id();
let mut payer_balance=1;let mut system_balance=1;let mut payer_data=[];let mut system_data=[];
let payer=AccountInfo::new(&payer_key,true,true,&mut payer_balance,&mut payer_data,&system_key,false,0);
let system=AccountInfo::new(&system_key,false,false,&mut system_balance,&mut system_data,&loader,true,0);
assert!(require_payer_and_system_program(&payer,&system).is_ok());
assert_eq!(require_payer_and_system_program(&account,&system),Err(PoolV1ProgramError::InvalidPayer.into()));
drop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_payer_1768() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;1768]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&foreign,false,0);
let payer_key=Pubkey::new_from_array([9;32]);let system_key=system_program::id();let loader=native_loader::id();
let mut payer_balance=1;let mut system_balance=1;let mut payer_data=[];let mut system_data=[];
let payer=AccountInfo::new(&payer_key,true,true,&mut payer_balance,&mut payer_data,&system_key,false,0);
let system=AccountInfo::new(&system_key,false,false,&mut system_balance,&mut system_data,&loader,true,0);
assert!(require_payer_and_system_program(&payer,&system).is_ok());
assert_eq!(require_payer_and_system_program(&account,&system),Err(PoolV1ProgramError::InvalidPayer.into()));
drop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_token_program_192() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;192]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&id,false,0);
assert_eq!(require_token_program_account(&account),Err(PoolV1ProgramError::InvalidTokenProgram.into()));
drop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_token_program_1768() {
let id=Pubkey::new_from_array([7;32]); let key=Pubkey::new_from_array([8;32]);
let foreign=Pubkey::new_from_array([6;32]);
let mut bytes: [u8;1768]=kani::any(); let probe:usize=kani::any(); kani::assume(probe<bytes.len()); let before=bytes[probe];
let mut balance:u64=kani::any(); let original_balance=balance;
let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&foreign,false,0);
assert_eq!(require_token_program_account(&account),Err(PoolV1ProgramError::InvalidTokenProgram.into()));
drop(account); assert!(bytes[probe]==before); assert!(balance==original_balance);
}

}
