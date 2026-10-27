
#[cfg(kani)]
mod PoolN_prefixes {
use super::*;
fn PoolN_fixture(tag:u8)->Vec<u8> {
 use aspis_core::field::M31;
 use aspis_statement::pool_v1::*;
 use crate::instruction::*;
 let d=[M31(1);8];
 let initial=crate::state::PoolInitializationV1{asset_mint:[9;32],token_program:crate::vault::LEGACY_SPL_TOKEN_PROGRAM_ID.to_bytes(),asset_id:M31(4),deployment_domain:[5;32],verifier_policy:VerifierPolicyV1{flags:1,registry_program:[6;32],registry_authority:[0;32],policy_binding:[7;32]}};
 if tag==0 { return encode_initialize_instruction_v1(&initial).unwrap().to_vec(); }
 if tag==5 { return crate::pair_forest::encode_pair_forest_initialize_instruction_v1(&initial).unwrap().to_vec(); }
 if tag==6||tag==7 {let mut v=vec![0u8;80];v[..4].copy_from_slice(if tag==6{b"ASDI"}else{b"AS8D"});v[4]=1;v[40]=1;return v;}
 let envelope=HistoricalAnchorEnvelopeV1{transition_kind:PoolV1TransitionKind::PrivateTransfer,pool:[1;32],deployment_domain:[2;32],anchor_sequence:7,anchor_root:d,nullifier:d,verifier_profile:[3;32],verifier_release:[4;32]};
 let public=PoolV1PrivateTransferPublicV1{pool:envelope.pool,deployment_domain:envelope.deployment_domain,anchor_sequence:envelope.anchor_sequence,anchor_root:d,nullifier:d,asset_id:M31(7),recipient_commitment:d,change_commitment:d};
 if tag==8 {let request=PoolV1PairForestTerminalRequestV1{verifier_profile:[3;32],verifier_release:[4;32],pool_program:[5;32],public:PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public)};let mut v=encode_pool_v1_pair_forest_terminal_request_v1(&request).unwrap().to_vec();v.extend_from_slice(&[0;4]);return v;}
 if tag==4 {let payload=encode_pool_v1_private_transfer_public_v1(&public).unwrap();return crate::settle_prepared_instruction::encode_settle_prepared_instruction_v1(PoolV1TransitionKind::PrivateTransfer,&payload).unwrap().to_vec();}
 if tag==2 {let mut e=envelope;e.transition_kind=PoolV1TransitionKind::Withdrawal;let w=WithdrawalStatementV1{pool:e.pool,deployment_domain:e.deployment_domain,anchor_sequence:e.anchor_sequence,anchor_root:d,nullifier:d,asset_id:M31(7),amount:25,destination_token_account:[5;32],change_commitment:d};return encode_withdrawal_instruction_v1(&e,&w).unwrap().to_vec();}
 let t=PrivateTransferStatementV1{pool:envelope.pool,deployment_domain:envelope.deployment_domain,anchor_sequence:envelope.anchor_sequence,anchor_root:d,nullifier:d,asset_id:M31(7),recipient_commitment:d,change_commitment:d};
 let spend=encode_private_transfer_instruction_v1(&envelope,&t).unwrap();
 if tag==3 {return crate::prepared_settlement_instruction::encode_prepare_settlement_instruction_v1(PoolV1TransitionKind::PrivateTransfer,11,12,&spend).unwrap().to_vec();}
 spend.to_vec()
}

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
 let instruction=PoolN_fixture(5);
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
 let instruction=PoolN_fixture(5);
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
 let instruction=PoolN_fixture(7);
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
 let instruction=PoolN_fixture(7);
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
 let instruction=PoolN_fixture(8);
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
 let instruction=PoolN_fixture(8);
 let result=PoolN_ASQ8_prefix(&id,&accounts,&instruction);
 assert!(result.is_err());
 kani::cover!(result==Err(ProgramError::IncorrectProgramId),"type/owner rejection reached");
 drop(accounts);drop(cp);assert!(bytes[0]==before);assert!(balance==initial_balance);
}

}
