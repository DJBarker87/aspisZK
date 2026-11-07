import NMX_R2_ScalarCarrier
set_option autoImplicit false
namespace NMX_R2_ErrorInverse
open Aeneas Aeneas.Std AdapterRw NMX_R2_Carrier NMX_R2_ScalarCarrier

def fromWord (w : UInt32) : U32 := UScalar.ofNatCore w.toNat (UInt32.toNat_lt w)

theorem word_roundtrip (w : U32) : fromWord (word w) = w := by
 apply UScalar.eq_of_val_eq
 simp only [fromWord,UScalar.ofNatCore_val_eq,word_value]

def fromError : RSL.ProgramError → solana_program_error.ProgramError
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

theorem error_roundtrip (e : solana_program_error.ProgramError) : fromError (error e) = e := by
 cases e <;> simp only [fromError,error,word_roundtrip]

theorem injective : Function.Injective error := by
 intro a b same
 have inverse := congrArg fromError same
 simpa only [error_roundtrip] using inverse
#print axioms word_roundtrip
#print axioms error_roundtrip
#print axioms injective
end NMX_R2_ErrorInverse
