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
use solana_sdk_ids::{system_program,native_loader};
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum PoolV1ProgramError {
    InvalidAccountType = 0x4153_2001,
    InvalidRootPageAddress = 0x4153_2002,
    StateHistoryMismatch = 0x4153_2003,
    TreeFull = 0x4153_2004,
    InsufficientTreeCapacity = 0x4153_2005,
    UnexpectedRootPage = 0x4153_2006,
    NonCanonicalLeaf = 0x4153_2007,
    ArithmeticOverflow = 0x4153_2008,
    InvalidPoolStateAddress = 0x4153_2009,
    InvalidVerifierRegistryAddress = 0x4153_200A,
    InvalidVerifierEntryAddress = 0x4153_200B,
    InvalidVerifierRegistry = 0x4153_200C,
    InvalidVerifierEntry = 0x4153_200D,
    VerifierRegistryPaused = 0x4153_200E,
    VerifierEntryInactive = 0x4153_200F,
    VerifierEntryNotActiveYet = 0x4153_2010,
    VerifierEntryRetired = 0x4153_2011,
    VerifierSelectionMismatch = 0x4153_2012,
    InvalidTokenProgram = 0x4153_2013,
    InvalidMint = 0x4153_2014,
    InvalidTokenAccount = 0x4153_2015,
    InvalidVaultAuthority = 0x4153_2016,
    InvalidVaultTokenAddress = 0x4153_2017,
    InvalidDepositAmount = 0x4153_2018,
    InsufficientDepositFunds = 0x4153_2019,
    UnsupportedTokenConfiguration = 0x4153_201A,
    InvalidEncryptedNotePayload = 0x4153_201B,
    TokenBalanceDeltaMismatch = 0x4153_201C,
    InvalidSourceAuthority = 0x4153_201D,
    InvalidHistoricalAnchorEnvelope = 0x4153_201E,
    HistoricalAnchorIdentityMismatch = 0x4153_201F,
    HistoricalAnchorSelectionMismatch = 0x4153_2020,
    HistoricalAnchorInFuture = 0x4153_2021,
    InvalidHistoricalAnchorPage = 0x4153_2022,
    HistoricalAnchorRootMismatch = 0x4153_2023,
    InvalidNullifierMarkerAddress = 0x4153_2024,
    InvalidNullifierMarkerAccount = 0x4153_2025,
    NullifierAlreadyConsumed = 0x4153_2026,
    InvalidVerifierProgramAccount = 0x4153_2027,
    InvalidVerifierProofAccount = 0x4153_2028,
    VerifierProofBindingMismatch = 0x4153_2029,
    InvalidVerifierDispatchEnvelope = 0x4153_202A,
    VerifierDispatchIdentityMismatch = 0x4153_202B,
    InvalidVerifierReturnProgram = 0x4153_202C,
    InvalidVerifierReturnData = 0x4153_202D,
    VerifierResultBindingMismatch = 0x4153_202E,
    MissingVerifierReturnData = 0x4153_202F,
    InvalidWithdrawalAmount = 0x4153_2030,
    InsufficientVaultFunds = 0x4153_2031,
    InvalidDestinationTokenAccount = 0x4153_2032,
    InvalidSystemProgram = 0x4153_2033,
    InvalidPayer = 0x4153_2034,
    InvalidFreshAccount = 0x4153_2035,
    CpiInvocationForbidden = 0x4153_2036,
}

impl From<PoolV1ProgramError> for ProgramError {
    fn from(error: PoolV1ProgramError) -> Self {
        Self::Custom(error as u32)
    }
}

pub(crate) fn require_payer_and_system_program(
    payer: &AccountInfo<'_>,
    system_program_account: &AccountInfo<'_>,
) -> ProgramResult {
    if !payer.is_signer
        || !payer.is_writable
        || payer.executable
        || payer.owner != &system_program::id()
    {
        return Err(PoolV1ProgramError::InvalidPayer.into());
    }
    if system_program_account.key != &system_program::id()
        || system_program_account.owner != &native_loader::id()
        || !system_program_account.executable
        || system_program_account.is_signer
        || system_program_account.is_writable
    {
        return Err(PoolV1ProgramError::InvalidSystemProgram.into());
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

#[kani::proof]
#[kani::unwind(40)]
fn PoolS2_payer_system_exact(){
 let pk=Pubkey::new_from_array(kani::any());let sk=Pubkey::new_from_array(kani::any());let po=Pubkey::new_from_array(kani::any());let so=Pubkey::new_from_array(kani::any());let flags:[[bool;3];2]=kani::any();
 let mut pl:u64=kani::any();let mut sl:u64=kani::any();let mut pd:[u8;1]=kani::any();let mut sd:[u8;1]=kani::any();
 let p=AccountInfo::new(&pk,flags[0][0],flags[0][1],&mut pl,&mut pd,&po,flags[0][2],0);
 let s=AccountInfo::new(&sk,flags[1][0],flags[1][1],&mut sl,&mut sd,&so,flags[1][2],0);
 let system=Pubkey::new_from_array([0;32]);let loader=Pubkey::new_from_array([5, 135, 132, 191, 20, 139, 164, 40, 47, 176, 18, 87, 72, 136, 169, 241, 83, 160, 125, 173, 247, 101, 192, 69, 92, 154, 151, 3, 128, 0, 0, 0]);
 let payer_ok=flags[0][0]&&flags[0][1]&&!flags[0][2]&&po==system;
 let system_ok=sk==system&&so==loader&&flags[1][2]&&!flags[1][0]&&!flags[1][1];
 let expected=if !payer_ok{Err(ProgramError::Custom(0x41532034))}else if !system_ok{Err(ProgramError::Custom(0x41532033))}else{Ok(())};
 assert!(require_payer_and_system_program(&p,&s)==expected);
}

}
