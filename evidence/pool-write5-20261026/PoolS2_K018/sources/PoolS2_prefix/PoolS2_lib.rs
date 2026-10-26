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
fn require_exact_account_count(accounts: &[AccountInfo<'_>], expected: usize) -> ProgramResult {
    if accounts.len() != expected {
        return Err(if accounts.len() < expected {
            ProgramError::NotEnoughAccountKeys
        } else {
            ProgramError::InvalidArgument
        });
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

#[kani::proof]
#[kani::unwind(40)]
fn PoolS2_count_exact(){
 let keys_bytes:[[u8;32];13]=kani::any();let keys=keys_bytes.map(Pubkey::new_from_array);let owner=Pubkey::new_from_array(kani::any());
 let mut lamports:[u64;13]=kani::any();let mut data:[[u8;1];13]=kani::any();
 let accounts:Vec<_>=keys.iter().zip(lamports.iter_mut()).zip(data.iter_mut()).map(|((key,lamports),data)|AccountInfo::new(key,false,false,lamports,data,&owner,false,0)).collect();
 let n:usize=kani::any();kani::assume(n<=13);
 let expected=if n<12{Err(ProgramError::NotEnoughAccountKeys)}else if n>12{Err(ProgramError::InvalidArgument)}else{Ok(())};
 assert!(require_exact_account_count(&accounts[..n],12)==expected);
}

#[kani::proof]
#[kani::unwind(40)]
fn PoolS2_unique_fixed(){
 let raw:[[u8;32];12]=kani::any();let flags:[[bool;3];12]=kani::any();
 let owner=Pubkey::new_from_array(kani::any());let mut funds:[u64;12]=kani::any();let mut payload:[[u8;1];12]=kani::any();
let k0=Pubkey::new_from_array(raw[0]);
let k1=Pubkey::new_from_array(raw[1]);
let k2=Pubkey::new_from_array(raw[2]);
let k3=Pubkey::new_from_array(raw[3]);
let k4=Pubkey::new_from_array(raw[4]);
let k5=Pubkey::new_from_array(raw[5]);
let k6=Pubkey::new_from_array(raw[6]);
let k7=Pubkey::new_from_array(raw[7]);
let k8=Pubkey::new_from_array(raw[8]);
let k9=Pubkey::new_from_array(raw[9]);
let k10=Pubkey::new_from_array(raw[10]);
let k11=Pubkey::new_from_array(raw[11]);
let [l0,l1,l2,l3,l4,l5,l6,l7,l8,l9,l10,l11]=&mut funds;
let [d0,d1,d2,d3,d4,d5,d6,d7,d8,d9,d10,d11]=&mut payload;
let accounts=[AccountInfo::new(&k0,flags[0][0],flags[0][1],l0,d0,&owner,flags[0][2],0),AccountInfo::new(&k1,flags[1][0],flags[1][1],l1,d1,&owner,flags[1][2],0),AccountInfo::new(&k2,flags[2][0],flags[2][1],l2,d2,&owner,flags[2][2],0),AccountInfo::new(&k3,flags[3][0],flags[3][1],l3,d3,&owner,flags[3][2],0),AccountInfo::new(&k4,flags[4][0],flags[4][1],l4,d4,&owner,flags[4][2],0),AccountInfo::new(&k5,flags[5][0],flags[5][1],l5,d5,&owner,flags[5][2],0),AccountInfo::new(&k6,flags[6][0],flags[6][1],l6,d6,&owner,flags[6][2],0),AccountInfo::new(&k7,flags[7][0],flags[7][1],l7,d7,&owner,flags[7][2],0),AccountInfo::new(&k8,flags[8][0],flags[8][1],l8,d8,&owner,flags[8][2],0),AccountInfo::new(&k9,flags[9][0],flags[9][1],l9,d9,&owner,flags[9][2],0),AccountInfo::new(&k10,flags[10][0],flags[10][1],l10,d10,&owner,flags[10][2],0),AccountInfo::new(&k11,flags[11][0],flags[11][1],l11,d11,&owner,flags[11][2],0)];
if require_unique_accounts(&accounts).is_ok(){assert!(raw[0]!=raw[9]);}
}

#[kani::proof]
#[kani::unwind(40)]
fn PoolS2_unique_fixed_projection(){
 let raw:[[u8;32];12]=kani::any();let flags:[[bool;3];12]=kani::any();
 let owner=Pubkey::new_from_array(kani::any());let mut funds:[u64;12]=kani::any();let mut payload:[[u8;1];12]=kani::any();
let k0=Pubkey::new_from_array(raw[0]);
let k1=Pubkey::new_from_array(raw[1]);
let k2=Pubkey::new_from_array(raw[2]);
let k3=Pubkey::new_from_array(raw[3]);
let k4=Pubkey::new_from_array(raw[4]);
let k5=Pubkey::new_from_array(raw[5]);
let k6=Pubkey::new_from_array(raw[6]);
let k7=Pubkey::new_from_array(raw[7]);
let k8=Pubkey::new_from_array(raw[8]);
let k9=Pubkey::new_from_array(raw[9]);
let k10=Pubkey::new_from_array(raw[10]);
let k11=Pubkey::new_from_array(raw[11]);
let [l0,l1,l2,l3,l4,l5,l6,l7,l8,l9,l10,l11]=&mut funds;
let [d0,d1,d2,d3,d4,d5,d6,d7,d8,d9,d10,d11]=&mut payload;
let accounts=[AccountInfo::new(&k0,flags[0][0],flags[0][1],l0,d0,&owner,flags[0][2],0),AccountInfo::new(&k1,flags[1][0],flags[1][1],l1,d1,&owner,flags[1][2],0),AccountInfo::new(&k2,flags[2][0],flags[2][1],l2,d2,&owner,flags[2][2],0),AccountInfo::new(&k3,flags[3][0],flags[3][1],l3,d3,&owner,flags[3][2],0),AccountInfo::new(&k4,flags[4][0],flags[4][1],l4,d4,&owner,flags[4][2],0),AccountInfo::new(&k5,flags[5][0],flags[5][1],l5,d5,&owner,flags[5][2],0),AccountInfo::new(&k6,flags[6][0],flags[6][1],l6,d6,&owner,flags[6][2],0),AccountInfo::new(&k7,flags[7][0],flags[7][1],l7,d7,&owner,flags[7][2],0),AccountInfo::new(&k8,flags[8][0],flags[8][1],l8,d8,&owner,flags[8][2],0),AccountInfo::new(&k9,flags[9][0],flags[9][1],l9,d9,&owner,flags[9][2],0),AccountInfo::new(&k10,flags[10][0],flags[10][1],l10,d10,&owner,flags[10][2],0),AccountInfo::new(&k11,flags[11][0],flags[11][1],l11,d11,&owner,flags[11][2],0)];
assert!(require_unique_accounts(&accounts).is_ok()==pools2_ref::unique_keys(&raw));
}

#[kani::proof]
#[kani::unwind(40)]
fn PoolS2_count_fixed(){
 let raw:[[u8;32];13]=kani::any();let flags:[[bool;3];13]=kani::any();
 let owner=Pubkey::new_from_array(kani::any());let mut funds:[u64;13]=kani::any();let mut payload:[[u8;1];13]=kani::any();
let k0=Pubkey::new_from_array(raw[0]);
let k1=Pubkey::new_from_array(raw[1]);
let k2=Pubkey::new_from_array(raw[2]);
let k3=Pubkey::new_from_array(raw[3]);
let k4=Pubkey::new_from_array(raw[4]);
let k5=Pubkey::new_from_array(raw[5]);
let k6=Pubkey::new_from_array(raw[6]);
let k7=Pubkey::new_from_array(raw[7]);
let k8=Pubkey::new_from_array(raw[8]);
let k9=Pubkey::new_from_array(raw[9]);
let k10=Pubkey::new_from_array(raw[10]);
let k11=Pubkey::new_from_array(raw[11]);
let k12=Pubkey::new_from_array(raw[12]);
let [l0,l1,l2,l3,l4,l5,l6,l7,l8,l9,l10,l11,l12]=&mut funds;
let [d0,d1,d2,d3,d4,d5,d6,d7,d8,d9,d10,d11,d12]=&mut payload;
let accounts=[AccountInfo::new(&k0,flags[0][0],flags[0][1],l0,d0,&owner,flags[0][2],0),AccountInfo::new(&k1,flags[1][0],flags[1][1],l1,d1,&owner,flags[1][2],0),AccountInfo::new(&k2,flags[2][0],flags[2][1],l2,d2,&owner,flags[2][2],0),AccountInfo::new(&k3,flags[3][0],flags[3][1],l3,d3,&owner,flags[3][2],0),AccountInfo::new(&k4,flags[4][0],flags[4][1],l4,d4,&owner,flags[4][2],0),AccountInfo::new(&k5,flags[5][0],flags[5][1],l5,d5,&owner,flags[5][2],0),AccountInfo::new(&k6,flags[6][0],flags[6][1],l6,d6,&owner,flags[6][2],0),AccountInfo::new(&k7,flags[7][0],flags[7][1],l7,d7,&owner,flags[7][2],0),AccountInfo::new(&k8,flags[8][0],flags[8][1],l8,d8,&owner,flags[8][2],0),AccountInfo::new(&k9,flags[9][0],flags[9][1],l9,d9,&owner,flags[9][2],0),AccountInfo::new(&k10,flags[10][0],flags[10][1],l10,d10,&owner,flags[10][2],0),AccountInfo::new(&k11,flags[11][0],flags[11][1],l11,d11,&owner,flags[11][2],0),AccountInfo::new(&k12,flags[12][0],flags[12][1],l12,d12,&owner,flags[12][2],0)];
let n:usize=kani::any();kani::assume(n<=13);
let expected=if n<12{Err(ProgramError::NotEnoughAccountKeys)}else if n>12{Err(ProgramError::InvalidArgument)}else{Ok(())};
assert!(require_exact_account_count(&accounts[..n],12)==expected);
}

}
