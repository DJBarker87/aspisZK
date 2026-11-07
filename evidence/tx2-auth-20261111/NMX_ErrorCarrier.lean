import NMX_InverseScalars
set_option autoImplicit false
namespace NMX_ErrorCarrier
open Aeneas Aeneas.Std AdapterRw NMX_Carrier NMX_InverseScalars
/-- No ProgramError tag/payload is collapsed, including Custom and String. -/
def inverse : RSL.ProgramError → solana_program_error.ProgramError
 | .custom n => .Custom (fromWord n)
 | .invalidArgument => .InvalidArgument
 | .invalidInstructionData => .InvalidInstructionData
 | .invalidAccountData => .InvalidAccountData
 | .accountDataTooSmall => .AccountDataTooSmall
 | .insufficientFunds => .InsufficientFunds
 | .incorrectProgramId => .IncorrectProgramId
 | .missingRequiredSignature => .MissingRequiredSignature
 | .accountAlreadyInitialized => .AccountAlreadyInitialized
 | .uninitializedAccount => .UninitializedAccount
 | .notEnoughAccountKeys => .NotEnoughAccountKeys
 | .accountBorrowFailed => .AccountBorrowFailed
 | .maxSeedLengthExceeded => .MaxSeedLengthExceeded
 | .invalidSeeds => .InvalidSeeds
 | .borshIoError msg => .BorshIoError msg
 | .accountNotRentExempt => .AccountNotRentExempt
 | .unsupportedSysvar => .UnsupportedSysvar
 | .illegalOwner => .IllegalOwner
 | .maxAccountsDataAllocationsExceeded => .MaxAccountsDataAllocationsExceeded
 | .invalidRealloc => .InvalidRealloc
 | .maxInstructionTraceLengthExceeded => .MaxInstructionTraceLengthExceeded
 | .builtinProgramsMustConsumeComputeUnits => .BuiltinProgramsMustConsumeComputeUnits
 | .invalidAccountOwner => .InvalidAccountOwner
 | .arithmeticOverflow => .ArithmeticOverflow
 | .immutable => .Immutable
 | .incorrectAuthority => .IncorrectAuthority

theorem roundtrip (e : solana_program_error.ProgramError) : inverse (error e) = e := by
 cases e <;> simp only [inverse,error,word_roundtrip]

theorem canonical_roundtrip (e : RSL.ProgramError) : error (inverse e) = e := by
 cases e <;> simp only [inverse,error,native_word_roundtrip]

theorem injective : Function.Injective error := by
 intro a b same
 have decoded := congrArg inverse same
 simpa only [roundtrip] using decoded
#print axioms roundtrip
#print axioms canonical_roundtrip
#print axioms injective
end NMX_ErrorCarrier
