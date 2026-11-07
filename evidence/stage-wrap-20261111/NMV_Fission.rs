// NMV source-fission descriptors. Window laws are interpreted in Lean.
#![allow(non_upper_case_globals)]
pub type Pubkey = [u8;32];
pub type ProgramResult = Result<(),ProgramError>;
pub struct Clock { pub slot: u64 }
pub enum ProgramError {
    /// Allows on-chain programs to implement program-specific error types and see them returned
    /// by the Solana runtime. A program-specific error may be any type that is represented as
    /// or serialized to a u32 integer.
    Custom(u32),
    InvalidArgument,
    InvalidInstructionData,
    InvalidAccountData,
    AccountDataTooSmall,
    InsufficientFunds,
    IncorrectProgramId,
    MissingRequiredSignature,
    AccountAlreadyInitialized,
    UninitializedAccount,
    NotEnoughAccountKeys,
    AccountBorrowFailed,
    MaxSeedLengthExceeded,
    InvalidSeeds,
    BorshIoError(String),
    AccountNotRentExempt,
    UnsupportedSysvar,
    IllegalOwner,
    MaxAccountsDataAllocationsExceeded,
    InvalidRealloc,
    MaxInstructionTraceLengthExceeded,
    BuiltinProgramsMustConsumeComputeUnits,
    InvalidAccountOwner,
    ArithmeticOverflow,
    Immutable,
    IncorrectAuthority,
}

pub trait WriteWindow<L> { fn copy_from_slice(self, log: &mut L, source: &[u8]); }
pub trait Windows: Sized {
    type Account;
    type Owned;
    type Write: WriteWindow<Self>;
    fn snapshot(log: &mut Self, account: &Self::Account, length1: usize, length2: usize) -> Self::Owned;
    fn stage1_owned(log: &mut Self, program: &Pubkey, accounts: &[Self::Owned], data: &[u8]) -> Result<Vec<u8>,ProgramError>;
    fn stage2_owned(log: &mut Self, program: &Pubkey, accounts: &[Self::Owned], data: &[u8], slot: Result<u64,ProgramError>) -> ProgramResult;
    fn try_borrow_mut_data(log: &mut Self, account: &Self::Account) -> Result<Self::Write,ProgramError>;
    fn set_return_data(log: &mut Self, data: &[u8]);
    fn clock_get(log: &mut Self) -> Result<Clock,ProgramError>;
}
pub mod verifier { pub const PROOF_BYTES: usize = 57607; }
pub const POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES: usize = 688;
pub const POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES: usize = 1880;
pub const CHECKPOINT_TAIL_BYTES: usize = 1768;
pub const POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES: usize = 384;
pub const POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES: usize = 192;
pub const POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES: usize = 768;
pub const POOL_V1_VERIFIER_REGISTRY_BYTES: usize = 128;
pub const POOL_V1_VERIFIER_REGISTRY_V2_BYTES: usize = 256;
pub const POOL_V1_VERIFIER_ENTRY_BYTES: usize = 192;
pub const POOL_V1_VERIFIER_ENTRY_V2_BYTES: usize = 320;
pub const POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC: [u8;4] = *b"ASQ8";
pub fn stage2<W: Windows>(log: &mut W, program_id: &Pubkey, accounts: &[W::Account], data: &[u8]) -> ProgramResult {
    if accounts.len() != 7 || data.get(..4) != Some(&POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC[..]) {
        return Err(ProgramError::InvalidInstructionData);
    }
    W::set_return_data(log, &[]);
    #[cfg(feature="cu-profiling")]
    { msg!("r1:pool-adapter-stage2-begin"); solana_program::log::sol_log_compute_units(); }
    let owned = [
        W::snapshot(log, &accounts[0], POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES + verifier::PROOF_BYTES, POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES + verifier::PROOF_BYTES),
        W::snapshot(log, &accounts[1], POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES, POOL_V1_PAIR_FOREST_MASTER_ACCOUNT_BYTES),
        W::snapshot(log, &accounts[2], POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES, POOL_V1_PAIR_FOREST_CHECKPOINT_ACCOUNT_BYTES),
        W::snapshot(log, &accounts[3], POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES, POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES),
        W::snapshot(log, &accounts[4], POOL_V1_VERIFIER_REGISTRY_BYTES, POOL_V1_VERIFIER_REGISTRY_V2_BYTES),
        W::snapshot(log, &accounts[5], POOL_V1_VERIFIER_ENTRY_BYTES, POOL_V1_VERIFIER_ENTRY_V2_BYTES),
        W::snapshot(log, &accounts[6], CHECKPOINT_TAIL_BYTES, CHECKPOINT_TAIL_BYTES),
    ];
    let current_slot = match W::clock_get(log) { Ok(clock) => Ok(clock.slot), Err(error) => Err(error) };
    W::stage2_owned(log, program_id, &owned, data, current_slot)
}
pub fn stage1<W: Windows>(log: &mut W, program_id: &Pubkey, accounts: &[W::Account], data: &[u8]) -> ProgramResult {
    if !(data == &[3, 10] || data == &[3, 11]) || accounts.len() != 3 {
        return Err(ProgramError::InvalidInstructionData);
    }
    let owned = [
        W::snapshot(log, &accounts[0], POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES + verifier::PROOF_BYTES, POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES + verifier::PROOF_BYTES),
        W::snapshot(log, &accounts[1], POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES, POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES),
        W::snapshot(log, &accounts[2], CHECKPOINT_TAIL_BYTES, CHECKPOINT_TAIL_BYTES),
    ];
    let checkpoint = W::stage1_owned(log, program_id, &owned, data)?;
    W::try_borrow_mut_data(log, &accounts[2])?.copy_from_slice(log, &checkpoint);
    #[cfg(feature="cu-profiling")]
    { msg!("r1:pool-adapter-stage1-checkpoint-written"); solana_program::log::sol_log_compute_units(); }
    Ok(())
}
