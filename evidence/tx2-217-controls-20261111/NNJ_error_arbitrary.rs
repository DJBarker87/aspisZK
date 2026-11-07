// cfg(kani)-only, in ProgramError's defining crate. Calibration constructors.
// All 26 tags and every Custom(u32) payload. BorshIoError payload bounded to
// at most 1 byte; no universal full-String/native havoc claim is made.
impl kani::Arbitrary for ProgramError {
    fn any() -> Self {
        match kani::any::<u8>() % 26 {
            0 => Self::Custom(kani::any()),
            1 => Self::InvalidArgument,
            2 => Self::InvalidInstructionData,
            3 => Self::InvalidAccountData,
            4 => Self::AccountDataTooSmall,
            5 => Self::InsufficientFunds,
            6 => Self::IncorrectProgramId,
            7 => Self::MissingRequiredSignature,
            8 => Self::AccountAlreadyInitialized,
            9 => Self::UninitializedAccount,
            10 => Self::NotEnoughAccountKeys,
            11 => Self::AccountBorrowFailed,
            12 => Self::MaxSeedLengthExceeded,
            13 => Self::InvalidSeeds,
            14 => Self::BorshIoError(kani::bounded_any::<String, 1>()),
            15 => Self::AccountNotRentExempt,
            16 => Self::UnsupportedSysvar,
            17 => Self::IllegalOwner,
            18 => Self::MaxAccountsDataAllocationsExceeded,
            19 => Self::InvalidRealloc,
            20 => Self::MaxInstructionTraceLengthExceeded,
            21 => Self::BuiltinProgramsMustConsumeComputeUnits,
            22 => Self::InvalidAccountOwner,
            23 => Self::ArithmeticOverflow,
            24 => Self::Immutable,
            _ => Self::IncorrectAuthority,
        }
    }
}
