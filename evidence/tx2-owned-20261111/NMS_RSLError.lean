import NMS_RSLScalars
set_option autoImplicit false
namespace NMS_RSLError
open Aeneas Aeneas.Std AdapterRw NMS_RSLScalars
abbrev Raw := solana_program_error.ProgramError

def error : Raw → RSL.ProgramError
 | .Custom x => .custom (u32 x)
 | .InvalidArgument => .invalidArgument
 | .InvalidInstructionData => .invalidInstructionData
 | .InvalidAccountData => .invalidAccountData
 | .AccountDataTooSmall => .accountDataTooSmall
 | .InsufficientFunds => .insufficientFunds
 | .IncorrectProgramId => .incorrectProgramId
 | .MissingRequiredSignature => .missingRequiredSignature
 | .AccountAlreadyInitialized => .accountAlreadyInitialized
 | .UninitializedAccount => .uninitializedAccount
 | .NotEnoughAccountKeys => .notEnoughAccountKeys
 | .AccountBorrowFailed => .accountBorrowFailed
 | .MaxSeedLengthExceeded => .maxSeedLengthExceeded
 | .InvalidSeeds => .invalidSeeds
 | .BorshIoError x => .borshIoError x
 | .AccountNotRentExempt => .accountNotRentExempt
 | .UnsupportedSysvar => .unsupportedSysvar
 | .IllegalOwner => .illegalOwner
 | .MaxAccountsDataAllocationsExceeded => .maxAccountsDataAllocationsExceeded
 | .InvalidRealloc => .invalidRealloc
 | .MaxInstructionTraceLengthExceeded => .maxInstructionTraceLengthExceeded
 | .BuiltinProgramsMustConsumeComputeUnits => .builtinProgramsMustConsumeComputeUnits
 | .InvalidAccountOwner => .invalidAccountOwner
 | .ArithmeticOverflow => .arithmeticOverflow
 | .Immutable => .immutable
 | .IncorrectAuthority => .incorrectAuthority

def raw : RSL.ProgramError → Raw
 | .custom x => .Custom (raw32 x)
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

theorem left (e : Raw) : raw (error e) = e := by cases e <;> rfl
theorem right (e : RSL.ProgramError) : error (raw e) = e := by cases e <;> rfl

def reply {A B : Type} (value : A → B) : core.result.Result A Raw → Except RSL.ProgramError B
 | .Ok a => .ok (value a)
 | .Err e => .error (error e)

#print axioms left
#print axioms right
end NMS_RSLError
