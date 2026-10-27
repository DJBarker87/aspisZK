use solana_program::{account_info::AccountInfo,entrypoint::ProgramResult,program_error::ProgramError,pubkey::Pubkey};
pub(crate) fn require_unique_accounts(accounts: &[AccountInfo<'_>]) -> ProgramResult {
    for left in 0..accounts.len() {
        for right in left + 1..accounts.len() {
            if accounts[left].key == accounts[right].key {
                return Err(ProgramError::InvalidArgument);
            }
        }
    }
    Ok(())
}

const POOL_V1_PAIR_FOREST_CHECKPOINT_INSTRUCTION_BYTES:usize=8;
const POOL_V1_PAIR_FOREST_CHECKPOINT_INSTRUCTION_MAGIC:[u8;4]=*b"AS8C";
const POOL_V1_INSTRUCTION_VERSION:u8=1;
const POOL_V1_PAIR_FOREST_LANE_COUNT:usize=8;
const POOL_V1_DIGEST_ENCODING_VERSION:u8=1;
pub fn encode_pair_forest_checkpoint_instruction_v1(
) -> [u8; POOL_V1_PAIR_FOREST_CHECKPOINT_INSTRUCTION_BYTES] {
    [
        POOL_V1_PAIR_FOREST_CHECKPOINT_INSTRUCTION_MAGIC[0],
        POOL_V1_PAIR_FOREST_CHECKPOINT_INSTRUCTION_MAGIC[1],
        POOL_V1_PAIR_FOREST_CHECKPOINT_INSTRUCTION_MAGIC[2],
        POOL_V1_PAIR_FOREST_CHECKPOINT_INSTRUCTION_MAGIC[3],
        POOL_V1_INSTRUCTION_VERSION,
        POOL_V1_PAIR_FOREST_LANE_COUNT as u8,
        POOL_V1_DIGEST_ENCODING_VERSION,
        0,
    ]
}

pub fn decode_pair_forest_checkpoint_instruction_v1(bytes: &[u8]) -> ProgramResult {
    if bytes != encode_pair_forest_checkpoint_instruction_v1() {
        return Err(ProgramError::InvalidInstructionData);
    }
    Ok(())
}
#[cfg(kani)] mod PoolS2_checks{use super::*;
#[kani::proof]
#[kani::unwind(80)]
fn PoolS2_unique_projection(){
 let keys_bytes:[[u8;32];12]=kani::any();let keys=keys_bytes.map(Pubkey::new_from_array);
 let owner=Pubkey::new_from_array(kani::any());let flags:[[bool;3];12]=kani::any();
 let mut lamports:[u64;12]=kani::any();let mut data:[[u8;1];12]=kani::any();
 let accounts:Vec<_>=keys.iter().zip(lamports.iter_mut()).zip(data.iter_mut()).enumerate().map(|(i,((key,lamports),data))|AccountInfo::new(key,flags[i][0],flags[i][1],lamports,data,&owner,flags[i][2],0)).collect();
 assert!(require_unique_accounts(&accounts).is_ok()==pools2_ref::unique_keys(&keys_bytes));
}
#[kani::proof]
#[kani::unwind(80)]
fn PoolS2_unique_master_checkpoint(){
 let keys_bytes:[[u8;32];12]=kani::any();let keys=keys_bytes.map(Pubkey::new_from_array);
 let owner=Pubkey::new_from_array(kani::any());let flags:[[bool;3];12]=kani::any();
 let mut lamports:[u64;12]=kani::any();let mut data:[[u8;1];12]=kani::any();
 let accounts:Vec<_>=keys.iter().zip(lamports.iter_mut()).zip(data.iter_mut()).enumerate().map(|(i,((key,lamports),data))|AccountInfo::new(key,flags[i][0],flags[i][1],lamports,data,&owner,flags[i][2],0)).collect();
 if require_unique_accounts(&accounts).is_ok(){assert!(keys_bytes[0]!=keys_bytes[9]);}
}

#[kani::proof]
#[kani::unwind(40)]
fn PoolS2_instruction_exact(){
 let raw:[u8;9]=kani::any();let n:usize=kani::any();kani::assume(n<=9);
 assert!(decode_pair_forest_checkpoint_instruction_v1(&raw[..n]).is_ok()==(n==8 && raw[..n]==[65,83,56,67,1,8,1,0]));
}

}
