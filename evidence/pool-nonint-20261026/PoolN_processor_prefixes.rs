
#[cfg(kani)]
mod PoolN_prefixes {
use super::*;

fn PoolN_ASDI_prefix(program_id: &Pubkey, accounts: &[AccountInfo<'_>], instruction_data: &[u8]) -> ProgramResult {
    let request = decode_deposit_top_level_v1(instruction_data)?;
    let pool = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    let state = load_canonical_pool_state(program_id, pool)?;
Ok(())
}

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_ASDI_prefix_192() {
 let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let cpkey=Pubkey::new_from_array([8;32]);
 let mut bytes:[u8;192]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
 let cp=AccountInfo::new(&cpkey,kani::any(),kani::any(),&mut balance,&mut bytes,&id,false,0);
 let keys:[Pubkey;1]=core::array::from_fn(|i|Pubkey::new_from_array([20+i as u8;32]));
 let mut balances=[0u64;1];let mut dummy=[[0u8;0];1];
 let mut accounts=Vec::new();
 for ((key,bal),data) in keys.iter().zip(balances.iter_mut()).zip(dummy.iter_mut()) {
   accounts.push(AccountInfo::new(key,false,false,bal,data,&id,false,0));
 }
 accounts[0]=cp.clone();
 let instruction:[u8;80]=kani::any();
 let result=PoolN_ASDI_prefix(&id,&accounts,&instruction);
 assert!(result.is_err());
 kani::cover!(result==Err(PoolV1ProgramError::InvalidAccountType.into()),"type/owner rejection reached");
 drop(accounts);drop(cp);assert!(bytes[0]==before);assert!(balance==initial_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_ASDI_prefix_1768() {
 let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let cpkey=Pubkey::new_from_array([8;32]);
 let mut bytes:[u8;1768]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
 let cp=AccountInfo::new(&cpkey,kani::any(),kani::any(),&mut balance,&mut bytes,&foreign,false,0);
 let keys:[Pubkey;1]=core::array::from_fn(|i|Pubkey::new_from_array([20+i as u8;32]));
 let mut balances=[0u64;1];let mut dummy=[[0u8;0];1];
 let mut accounts=Vec::new();
 for ((key,bal),data) in keys.iter().zip(balances.iter_mut()).zip(dummy.iter_mut()) {
   accounts.push(AccountInfo::new(key,false,false,bal,data,&id,false,0));
 }
 accounts[0]=cp.clone();
 let instruction:[u8;80]=kani::any();
 let result=PoolN_ASDI_prefix(&id,&accounts,&instruction);
 assert!(result.is_err());
 kani::cover!(result==Err(ProgramError::IncorrectProgramId),"type/owner rejection reached");
 drop(accounts);drop(cp);assert!(bytes[0]==before);assert!(balance==initial_balance);
}

fn PoolN_ASPT_prefix(program_id: &Pubkey, accounts: &[AccountInfo<'_>], instruction_data: &[u8]) -> ProgramResult {
    let decoded = decode_private_transfer_instruction_v1(instruction_data)?;
    let pool = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    let state = load_canonical_pool_state(program_id, pool)?;
Ok(())
}

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_ASPT_prefix_192() {
 let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let cpkey=Pubkey::new_from_array([8;32]);
 let mut bytes:[u8;192]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
 let cp=AccountInfo::new(&cpkey,kani::any(),kani::any(),&mut balance,&mut bytes,&id,false,0);
 let keys:[Pubkey;1]=core::array::from_fn(|i|Pubkey::new_from_array([20+i as u8;32]));
 let mut balances=[0u64;1];let mut dummy=[[0u8;0];1];
 let mut accounts=Vec::new();
 for ((key,bal),data) in keys.iter().zip(balances.iter_mut()).zip(dummy.iter_mut()) {
   accounts.push(AccountInfo::new(key,false,false,bal,data,&id,false,0));
 }
 accounts[0]=cp.clone();
 let instruction:[u8;crate::instruction::POOL_V1_SPEND_INSTRUCTION_BYTES]=kani::any();
 let result=PoolN_ASPT_prefix(&id,&accounts,&instruction);
 assert!(result.is_err());
 kani::cover!(result==Err(PoolV1ProgramError::InvalidAccountType.into()),"type/owner rejection reached");
 drop(accounts);drop(cp);assert!(bytes[0]==before);assert!(balance==initial_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_ASPT_prefix_1768() {
 let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let cpkey=Pubkey::new_from_array([8;32]);
 let mut bytes:[u8;1768]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
 let cp=AccountInfo::new(&cpkey,kani::any(),kani::any(),&mut balance,&mut bytes,&foreign,false,0);
 let keys:[Pubkey;1]=core::array::from_fn(|i|Pubkey::new_from_array([20+i as u8;32]));
 let mut balances=[0u64;1];let mut dummy=[[0u8;0];1];
 let mut accounts=Vec::new();
 for ((key,bal),data) in keys.iter().zip(balances.iter_mut()).zip(dummy.iter_mut()) {
   accounts.push(AccountInfo::new(key,false,false,bal,data,&id,false,0));
 }
 accounts[0]=cp.clone();
 let instruction:[u8;crate::instruction::POOL_V1_SPEND_INSTRUCTION_BYTES]=kani::any();
 let result=PoolN_ASPT_prefix(&id,&accounts,&instruction);
 assert!(result.is_err());
 kani::cover!(result==Err(ProgramError::IncorrectProgramId),"type/owner rejection reached");
 drop(accounts);drop(cp);assert!(bytes[0]==before);assert!(balance==initial_balance);
}

fn PoolN_ASWD_prefix(program_id: &Pubkey, accounts: &[AccountInfo<'_>], instruction_data: &[u8]) -> ProgramResult {
    let decoded = decode_withdrawal_instruction_v1(instruction_data)?;
    let pool = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    let state = load_canonical_pool_state(program_id, pool)?;
Ok(())
}

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_ASWD_prefix_192() {
 let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let cpkey=Pubkey::new_from_array([8;32]);
 let mut bytes:[u8;192]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
 let cp=AccountInfo::new(&cpkey,kani::any(),kani::any(),&mut balance,&mut bytes,&id,false,0);
 let keys:[Pubkey;1]=core::array::from_fn(|i|Pubkey::new_from_array([20+i as u8;32]));
 let mut balances=[0u64;1];let mut dummy=[[0u8;0];1];
 let mut accounts=Vec::new();
 for ((key,bal),data) in keys.iter().zip(balances.iter_mut()).zip(dummy.iter_mut()) {
   accounts.push(AccountInfo::new(key,false,false,bal,data,&id,false,0));
 }
 accounts[0]=cp.clone();
 let instruction:[u8;crate::instruction::POOL_V1_SPEND_INSTRUCTION_BYTES]=kani::any();
 let result=PoolN_ASWD_prefix(&id,&accounts,&instruction);
 assert!(result.is_err());
 kani::cover!(result==Err(PoolV1ProgramError::InvalidAccountType.into()),"type/owner rejection reached");
 drop(accounts);drop(cp);assert!(bytes[0]==before);assert!(balance==initial_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_ASWD_prefix_1768() {
 let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let cpkey=Pubkey::new_from_array([8;32]);
 let mut bytes:[u8;1768]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
 let cp=AccountInfo::new(&cpkey,kani::any(),kani::any(),&mut balance,&mut bytes,&foreign,false,0);
 let keys:[Pubkey;1]=core::array::from_fn(|i|Pubkey::new_from_array([20+i as u8;32]));
 let mut balances=[0u64;1];let mut dummy=[[0u8;0];1];
 let mut accounts=Vec::new();
 for ((key,bal),data) in keys.iter().zip(balances.iter_mut()).zip(dummy.iter_mut()) {
   accounts.push(AccountInfo::new(key,false,false,bal,data,&id,false,0));
 }
 accounts[0]=cp.clone();
 let instruction:[u8;crate::instruction::POOL_V1_SPEND_INSTRUCTION_BYTES]=kani::any();
 let result=PoolN_ASWD_prefix(&id,&accounts,&instruction);
 assert!(result.is_err());
 kani::cover!(result==Err(ProgramError::IncorrectProgramId),"type/owner rejection reached");
 drop(accounts);drop(cp);assert!(bytes[0]==before);assert!(balance==initial_balance);
}

fn PoolN_ASPP_prefix(program_id: &Pubkey, accounts: &[AccountInfo<'_>], instruction_data: &[u8]) -> ProgramResult {
    let request = decode_prepare_settlement_request_v1(instruction_data)?;
    let payer = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    let pool = accounts.get(1).ok_or(ProgramError::NotEnoughAccountKeys)?;
    // Preparation does not mutate the live Pool. Its source tree relation is
    // carried by the Pool program's inductive write invariant, so this path
    // retains every byte/PDA/ownership check while avoiding a redundant
    // depth-20 Poseidon reconstruction before computing the two new roots.
    let state = CanonicalPoolStateV1::decode_account_from_program_invariant(program_id, pool)?;
Ok(())
}

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_ASPP_prefix_192() {
 let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let cpkey=Pubkey::new_from_array([8;32]);
 let mut bytes:[u8;192]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
 let cp=AccountInfo::new(&cpkey,kani::any(),kani::any(),&mut balance,&mut bytes,&id,false,0);
 let keys:[Pubkey;2]=core::array::from_fn(|i|Pubkey::new_from_array([20+i as u8;32]));
 let mut balances=[0u64;2];let mut dummy=[[0u8;0];2];
 let mut accounts=Vec::new();
 for ((key,bal),data) in keys.iter().zip(balances.iter_mut()).zip(dummy.iter_mut()) {
   accounts.push(AccountInfo::new(key,false,false,bal,data,&id,false,0));
 }
 accounts[1]=cp.clone();
 let instruction:[u8;crate::prepared_settlement_instruction::POOL_V1_PREPARE_SETTLEMENT_INSTRUCTION_BYTES]=kani::any();
 let result=PoolN_ASPP_prefix(&id,&accounts,&instruction);
 assert!(result.is_err());
 kani::cover!(result==Err(PoolV1ProgramError::InvalidAccountType.into()),"type/owner rejection reached");
 drop(accounts);drop(cp);assert!(bytes[0]==before);assert!(balance==initial_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_ASPP_prefix_1768() {
 let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let cpkey=Pubkey::new_from_array([8;32]);
 let mut bytes:[u8;1768]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
 let cp=AccountInfo::new(&cpkey,kani::any(),kani::any(),&mut balance,&mut bytes,&foreign,false,0);
 let keys:[Pubkey;2]=core::array::from_fn(|i|Pubkey::new_from_array([20+i as u8;32]));
 let mut balances=[0u64;2];let mut dummy=[[0u8;0];2];
 let mut accounts=Vec::new();
 for ((key,bal),data) in keys.iter().zip(balances.iter_mut()).zip(dummy.iter_mut()) {
   accounts.push(AccountInfo::new(key,false,false,bal,data,&id,false,0));
 }
 accounts[1]=cp.clone();
 let instruction:[u8;crate::prepared_settlement_instruction::POOL_V1_PREPARE_SETTLEMENT_INSTRUCTION_BYTES]=kani::any();
 let result=PoolN_ASPP_prefix(&id,&accounts,&instruction);
 assert!(result.is_err());
 kani::cover!(result==Err(ProgramError::IncorrectProgramId),"type/owner rejection reached");
 drop(accounts);drop(cp);assert!(bytes[0]==before);assert!(balance==initial_balance);
}

fn PoolN_ASPF_prefix(program_id: &Pubkey, accounts: &[AccountInfo<'_>], instruction_data: &[u8]) -> ProgramResult {
    let instruction = decode_settle_prepared_instruction_v1(instruction_data)?;
    let plan_authority = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    let pool = accounts.get(1).ok_or(ProgramError::NotEnoughAccountKeys)?;
    let state = load_canonical_pool_state(program_id, pool)?;
Ok(())
}

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_ASPF_prefix_192() {
 let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let cpkey=Pubkey::new_from_array([8;32]);
 let mut bytes:[u8;192]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
 let cp=AccountInfo::new(&cpkey,kani::any(),kani::any(),&mut balance,&mut bytes,&id,false,0);
 let keys:[Pubkey;2]=core::array::from_fn(|i|Pubkey::new_from_array([20+i as u8;32]));
 let mut balances=[0u64;2];let mut dummy=[[0u8;0];2];
 let mut accounts=Vec::new();
 for ((key,bal),data) in keys.iter().zip(balances.iter_mut()).zip(dummy.iter_mut()) {
   accounts.push(AccountInfo::new(key,false,false,bal,data,&id,false,0));
 }
 accounts[1]=cp.clone();
 let instruction:[u8;crate::settle_prepared_instruction::POOL_V1_SETTLE_PREPARED_INSTRUCTION_BYTES]=kani::any();
 let result=PoolN_ASPF_prefix(&id,&accounts,&instruction);
 assert!(result.is_err());
 kani::cover!(result==Err(PoolV1ProgramError::InvalidAccountType.into()),"type/owner rejection reached");
 drop(accounts);drop(cp);assert!(bytes[0]==before);assert!(balance==initial_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_ASPF_prefix_1768() {
 let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let cpkey=Pubkey::new_from_array([8;32]);
 let mut bytes:[u8;1768]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
 let cp=AccountInfo::new(&cpkey,kani::any(),kani::any(),&mut balance,&mut bytes,&foreign,false,0);
 let keys:[Pubkey;2]=core::array::from_fn(|i|Pubkey::new_from_array([20+i as u8;32]));
 let mut balances=[0u64;2];let mut dummy=[[0u8;0];2];
 let mut accounts=Vec::new();
 for ((key,bal),data) in keys.iter().zip(balances.iter_mut()).zip(dummy.iter_mut()) {
   accounts.push(AccountInfo::new(key,false,false,bal,data,&id,false,0));
 }
 accounts[1]=cp.clone();
 let instruction:[u8;crate::settle_prepared_instruction::POOL_V1_SETTLE_PREPARED_INSTRUCTION_BYTES]=kani::any();
 let result=PoolN_ASPF_prefix(&id,&accounts,&instruction);
 assert!(result.is_err());
 kani::cover!(result==Err(ProgramError::IncorrectProgramId),"type/owner rejection reached");
 drop(accounts);drop(cp);assert!(bytes[0]==before);assert!(balance==initial_balance);
}

fn PoolN_ASIN_prefix(program_id: &Pubkey, accounts: &[AccountInfo<'_>], instruction_data: &[u8]) -> ProgramResult {
    let initialization = decode_initialize_instruction_v1(instruction_data)?;
    let [payer, pool, page_zero, mint, vault, token_program, system_program_account] = accounts
    else {
        return Err(if accounts.len() < 7 {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
    };
    require_unique_accounts(accounts)?;
    require_payer_and_system_program(payer, system_program_account)?;
Ok(())
}

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_ASIN_prefix_192() {
 let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let cpkey=Pubkey::new_from_array([8;32]);
 let mut bytes:[u8;192]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
 let cp=AccountInfo::new(&cpkey,kani::any(),kani::any(),&mut balance,&mut bytes,&id,false,0);
 let keys:[Pubkey;7]=core::array::from_fn(|i|Pubkey::new_from_array([20+i as u8;32]));
 let mut balances=[0u64;7];let mut dummy=[[0u8;0];7];
 let mut accounts=Vec::new();
 for ((key,bal),data) in keys.iter().zip(balances.iter_mut()).zip(dummy.iter_mut()) {
   accounts.push(AccountInfo::new(key,false,false,bal,data,&id,false,0));
 }
 accounts[0]=cp.clone();
 let instruction:[u8;crate::instruction::POOL_V1_INITIALIZE_INSTRUCTION_BYTES]=kani::any();
 let result=PoolN_ASIN_prefix(&id,&accounts,&instruction);
 assert!(result.is_err());
 kani::cover!(result==Err(PoolV1ProgramError::InvalidPayer.into()),"payer rejection reached");
 drop(accounts);drop(cp);assert!(bytes[0]==before);assert!(balance==initial_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_ASIN_prefix_1768() {
 let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let cpkey=Pubkey::new_from_array([8;32]);
 let mut bytes:[u8;1768]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
 let cp=AccountInfo::new(&cpkey,kani::any(),kani::any(),&mut balance,&mut bytes,&foreign,false,0);
 let keys:[Pubkey;7]=core::array::from_fn(|i|Pubkey::new_from_array([20+i as u8;32]));
 let mut balances=[0u64;7];let mut dummy=[[0u8;0];7];
 let mut accounts=Vec::new();
 for ((key,bal),data) in keys.iter().zip(balances.iter_mut()).zip(dummy.iter_mut()) {
   accounts.push(AccountInfo::new(key,false,false,bal,data,&id,false,0));
 }
 accounts[0]=cp.clone();
 let instruction:[u8;crate::instruction::POOL_V1_INITIALIZE_INSTRUCTION_BYTES]=kani::any();
 let result=PoolN_ASIN_prefix(&id,&accounts,&instruction);
 assert!(result.is_err());
 kani::cover!(result==Err(PoolV1ProgramError::InvalidPayer.into()),"payer rejection reached");
 drop(accounts);drop(cp);assert!(bytes[0]==before);assert!(balance==initial_balance);
}

}
