
#[cfg(kani)]
mod PoolN_prefixes {
use super::*;

fn PoolN_AS8I_prefix(program_id: &Pubkey, accounts: &[AccountInfo<'_>], instruction_data: &[u8]) -> ProgramResult {
    require_exact_account_count(accounts, POOL_V1_PAIR_FOREST_INITIALIZE_ACCOUNT_COUNT)?;
    require_unique_accounts(accounts)?;
    let initialization = decode_forest_initialization_box_v1(instruction_data)?;
    let master = &accounts[FOREST_MASTER_ACCOUNT_INDEX];
    let lanes = &accounts[FOREST_FIRST_LANE_ACCOUNT_INDEX
        ..FOREST_FIRST_LANE_ACCOUNT_INDEX + POOL_V1_PAIR_FOREST_LANE_COUNT];
    let mint = &accounts[FOREST_MINT_OR_CHECKPOINT_ACCOUNT_INDEX];
    let vault = &accounts[FOREST_INIT_VAULT_ACCOUNT_INDEX];
    let token_program = &accounts[FOREST_INIT_TOKEN_PROGRAM_ACCOUNT_INDEX];
    let payer = &accounts[FOREST_INIT_PAYER_ACCOUNT_INDEX];
    let system_program_account = &accounts[FOREST_INIT_SYSTEM_ACCOUNT_INDEX];
    require_payer_and_system_program(payer, system_program_account)?;
Ok(())
}

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_AS8I_prefix_192() {
 let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let cpkey=Pubkey::new_from_array([8;32]);
 let mut bytes:[u8;192]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
 let cp=AccountInfo::new(&cpkey,kani::any(),kani::any(),&mut balance,&mut bytes,&id,false,0);
 let keys:[Pubkey;14]=core::array::from_fn(|i|Pubkey::new_from_array([20+i as u8;32]));
 let mut balances=[0u64;14];let mut dummy=[[0u8;0];14];
 let mut accounts=Vec::new();
 for ((key,bal),data) in keys.iter().zip(balances.iter_mut()).zip(dummy.iter_mut()) {
   accounts.push(AccountInfo::new(key,false,false,bal,data,&id,false,0));
 }
 accounts[12]=cp.clone();
 let instruction:[u8;crate::instruction::POOL_V1_INITIALIZE_INSTRUCTION_BYTES]=kani::any();
 let result=PoolN_AS8I_prefix(&id,&accounts,&instruction);
 assert!(result.is_err());
 kani::cover!(result==Err(PoolV1ProgramError::InvalidPayer.into()),"payer rejection reached");
 drop(accounts);drop(cp);assert!(bytes[0]==before);assert!(balance==initial_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_AS8I_prefix_1768() {
 let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let cpkey=Pubkey::new_from_array([8;32]);
 let mut bytes:[u8;1768]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
 let cp=AccountInfo::new(&cpkey,kani::any(),kani::any(),&mut balance,&mut bytes,&foreign,false,0);
 let keys:[Pubkey;14]=core::array::from_fn(|i|Pubkey::new_from_array([20+i as u8;32]));
 let mut balances=[0u64;14];let mut dummy=[[0u8;0];14];
 let mut accounts=Vec::new();
 for ((key,bal),data) in keys.iter().zip(balances.iter_mut()).zip(dummy.iter_mut()) {
   accounts.push(AccountInfo::new(key,false,false,bal,data,&id,false,0));
 }
 accounts[12]=cp.clone();
 let instruction:[u8;crate::instruction::POOL_V1_INITIALIZE_INSTRUCTION_BYTES]=kani::any();
 let result=PoolN_AS8I_prefix(&id,&accounts,&instruction);
 assert!(result.is_err());
 kani::cover!(result==Err(PoolV1ProgramError::InvalidPayer.into()),"payer rejection reached");
 drop(accounts);drop(cp);assert!(bytes[0]==before);assert!(balance==initial_balance);
}

fn PoolN_AS8D_prefix(program_id: &Pubkey, accounts: &[AccountInfo<'_>], instruction_data: &[u8]) -> ProgramResult {
    let request = decode_pair_forest_deposit_instruction_v1(instruction_data)
        .map_err(|_| ProgramError::InvalidInstructionData)?;
    let master_account = accounts
        .get(FOREST_DEPOSIT_MASTER_ACCOUNT_INDEX)
        .ok_or(ProgramError::NotEnoughAccountKeys)?;
    let lane_account = accounts
        .get(FOREST_DEPOSIT_LANE_ACCOUNT_INDEX)
        .ok_or(ProgramError::NotEnoughAccountKeys)?;
    let current_page = accounts
        .get(FOREST_DEPOSIT_CURRENT_PAGE_ACCOUNT_INDEX)
        .ok_or(ProgramError::NotEnoughAccountKeys)?;
    let master = decode_terminal_master_box_v1(program_id, master_account)?;
Ok(())
}

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_AS8D_prefix_192() {
 let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let cpkey=Pubkey::new_from_array([8;32]);
 let mut bytes:[u8;192]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
 let cp=AccountInfo::new(&cpkey,kani::any(),kani::any(),&mut balance,&mut bytes,&id,false,0);
 let keys:[Pubkey;3]=core::array::from_fn(|i|Pubkey::new_from_array([20+i as u8;32]));
 let mut balances=[0u64;3];let mut dummy=[[0u8;0];3];
 let mut accounts=Vec::new();
 for ((key,bal),data) in keys.iter().zip(balances.iter_mut()).zip(dummy.iter_mut()) {
   accounts.push(AccountInfo::new(key,false,false,bal,data,&id,false,0));
 }
 accounts[0]=cp.clone();
 let instruction:[u8;80]=kani::any();
 let result=PoolN_AS8D_prefix(&id,&accounts,&instruction);
 assert!(result.is_err());
 kani::cover!(result==Err(PoolV1ProgramError::InvalidAccountType.into()),"type/owner rejection reached");
 drop(accounts);drop(cp);assert!(bytes[0]==before);assert!(balance==initial_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_AS8D_prefix_1768() {
 let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let cpkey=Pubkey::new_from_array([8;32]);
 let mut bytes:[u8;1768]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
 let cp=AccountInfo::new(&cpkey,kani::any(),kani::any(),&mut balance,&mut bytes,&foreign,false,0);
 let keys:[Pubkey;3]=core::array::from_fn(|i|Pubkey::new_from_array([20+i as u8;32]));
 let mut balances=[0u64;3];let mut dummy=[[0u8;0];3];
 let mut accounts=Vec::new();
 for ((key,bal),data) in keys.iter().zip(balances.iter_mut()).zip(dummy.iter_mut()) {
   accounts.push(AccountInfo::new(key,false,false,bal,data,&id,false,0));
 }
 accounts[0]=cp.clone();
 let instruction:[u8;80]=kani::any();
 let result=PoolN_AS8D_prefix(&id,&accounts,&instruction);
 assert!(result.is_err());
 kani::cover!(result==Err(ProgramError::IncorrectProgramId),"type/owner rejection reached");
 drop(accounts);drop(cp);assert!(bytes[0]==before);assert!(balance==initial_balance);
}

fn PoolN_ASQ8_prefix(program_id: &Pubkey, accounts: &[AccountInfo<'_>], instruction_data: &[u8]) -> ProgramResult {
    let (request_bytes, hints) = split_pair_forest_terminal_bump_hints_v1(instruction_data)?;
    let request = decode_terminal_request_box_v1(request_bytes)?;
    let master_account = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    let checkpoint_account = accounts.get(1).ok_or(ProgramError::NotEnoughAccountKeys)?;
    let lane_account = accounts.get(2).ok_or(ProgramError::NotEnoughAccountKeys)?;
    let master = decode_terminal_master_box_v1(program_id, master_account)?;
Ok(())
}

#[kani::proof]
#[kani::unwind(196)]
fn PoolN_ASQ8_prefix_192() {
 let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let cpkey=Pubkey::new_from_array([8;32]);
 let mut bytes:[u8;192]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
 let cp=AccountInfo::new(&cpkey,kani::any(),kani::any(),&mut balance,&mut bytes,&id,false,0);
 let keys:[Pubkey;3]=core::array::from_fn(|i|Pubkey::new_from_array([20+i as u8;32]));
 let mut balances=[0u64;3];let mut dummy=[[0u8;0];3];
 let mut accounts=Vec::new();
 for ((key,bal),data) in keys.iter().zip(balances.iter_mut()).zip(dummy.iter_mut()) {
   accounts.push(AccountInfo::new(key,false,false,bal,data,&id,false,0));
 }
 accounts[0]=cp.clone();
 let instruction:[u8;324]=kani::any();
 let result=PoolN_ASQ8_prefix(&id,&accounts,&instruction);
 assert!(result.is_err());
 kani::cover!(result==Err(PoolV1ProgramError::InvalidAccountType.into()),"type/owner rejection reached");
 drop(accounts);drop(cp);assert!(bytes[0]==before);assert!(balance==initial_balance);
}

#[kani::proof]
#[kani::unwind(1772)]
fn PoolN_ASQ8_prefix_1768() {
 let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let cpkey=Pubkey::new_from_array([8;32]);
 let mut bytes:[u8;1768]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
 let cp=AccountInfo::new(&cpkey,kani::any(),kani::any(),&mut balance,&mut bytes,&foreign,false,0);
 let keys:[Pubkey;3]=core::array::from_fn(|i|Pubkey::new_from_array([20+i as u8;32]));
 let mut balances=[0u64;3];let mut dummy=[[0u8;0];3];
 let mut accounts=Vec::new();
 for ((key,bal),data) in keys.iter().zip(balances.iter_mut()).zip(dummy.iter_mut()) {
   accounts.push(AccountInfo::new(key,false,false,bal,data,&id,false,0));
 }
 accounts[0]=cp.clone();
 let instruction:[u8;324]=kani::any();
 let result=PoolN_ASQ8_prefix(&id,&accounts,&instruction);
 assert!(result.is_err());
 kani::cover!(result==Err(ProgramError::IncorrectProgramId),"type/owner rejection reached");
 drop(accounts);drop(cp);assert!(bytes[0]==before);assert!(balance==initial_balance);
}

}
