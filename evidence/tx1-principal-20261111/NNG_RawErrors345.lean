import NNG_ProjectFrames345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_RawErrors345
open Aeneas Aeneas.Std NMT_345

def raw : RSL.ProgramError → PE
 | .custom x => .Custom (UScalar.ofNat x.toNat (by have h := x.toNat_lt; scalar_tac))
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
 | .borshIoError x => .BorshIoError x
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

theorem source (e : RSL.ProgramError) : pe (raw e)=e := by
 cases e <;> try rfl
 rename_i x
 apply congrArg RSL.ProgramError.custom
 apply UInt32.toNat_inj.mp
 change x.toNat % 4294967296=x.toNat
 exact Nat.mod_eq_of_lt x.toNat_lt
#print axioms source
end AspisR1.NNG_RawErrors345
