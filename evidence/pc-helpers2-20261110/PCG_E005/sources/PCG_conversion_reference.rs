#[derive(Clone,Copy)]
pub enum DepositInstructionFormatErrorV1 {
    WrongLength,
    WrongMagic,
    WrongVersion,
    NonZeroReserved,
    InvalidAmount,
    InvalidPayloadLength,
    NonCanonicalDigest,
}
#[derive(Clone,Copy)]
pub enum PoolInstructionFormatErrorV1 {
    WrongLength,
    WrongMagic,
    WrongVersion,
    WrongTransitionKind,
    WrongDigestEncoding,
    NonZeroReserved,
    InvalidEnvelope,
    EnvelopeStatementMismatch,
    InvalidPolicy,
    NonCanonicalField,
    InvalidWithdrawalAmount,
    InvalidDestination,
    InvalidDeposit,
}
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
pub fn reference287(_e:DepositInstructionFormatErrorV1)->PoolInstructionFormatErrorV1{PoolInstructionFormatErrorV1::InvalidDeposit}
pub fn reference288(_e:PoolInstructionFormatErrorV1)->ProgramError{ProgramError::InvalidInstructionData}
