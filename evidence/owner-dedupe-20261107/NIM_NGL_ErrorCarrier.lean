import NGJ_VERIFIER_IMPORT
import NGL_MetaReference.Types
import NIM_MapReference.Types
set_option autoImplicit false
namespace NGL_ErrorCarrier
open Aeneas Aeneas.Std Result
abbrev PE := AdapterRw.solana_program_error.ProgramError
def to_meta : PE → NGL_MetaReference.ProgramError
  | .Custom x => .Custom x
  | .InvalidArgument => .InvalidArgument
  | .InvalidInstructionData => .InvalidInstructionData
  | .InvalidAccountData => .InvalidAccountData
  | .AccountDataTooSmall => .AccountDataTooSmall
  | .InsufficientFunds => .InsufficientFunds
  | .IncorrectProgramId => .IncorrectProgramId
  | .MissingRequiredSignature => .MissingRequiredSignature
  | .AccountAlreadyInitialized => .AccountAlreadyInitialized
  | .UninitializedAccount => .UninitializedAccount
  | .NotEnoughAccountKeys => .NotEnoughAccountKeys
  | .AccountBorrowFailed => .AccountBorrowFailed
  | .MaxSeedLengthExceeded => .MaxSeedLengthExceeded
  | .InvalidSeeds => .InvalidSeeds
  | .BorshIoError x => .BorshIoError x
  | .AccountNotRentExempt => .AccountNotRentExempt
  | .UnsupportedSysvar => .UnsupportedSysvar
  | .IllegalOwner => .IllegalOwner
  | .MaxAccountsDataAllocationsExceeded => .MaxAccountsDataAllocationsExceeded
  | .InvalidRealloc => .InvalidRealloc
  | .MaxInstructionTraceLengthExceeded => .MaxInstructionTraceLengthExceeded
  | .BuiltinProgramsMustConsumeComputeUnits => .BuiltinProgramsMustConsumeComputeUnits
  | .InvalidAccountOwner => .InvalidAccountOwner
  | .ArithmeticOverflow => .ArithmeticOverflow
  | .Immutable => .Immutable
  | .IncorrectAuthority => .IncorrectAuthority
def from_meta : NGL_MetaReference.ProgramError → PE
  | .Custom x => .Custom x
  | .InvalidArgument => .InvalidArgument
  | .InvalidInstructionData => .InvalidInstructionData
  | .InvalidAccountData => .InvalidAccountData
  | .AccountDataTooSmall => .AccountDataTooSmall
  | .InsufficientFunds => .InsufficientFunds
  | .IncorrectProgramId => .IncorrectProgramId
  | .MissingRequiredSignature => .MissingRequiredSignature
  | .AccountAlreadyInitialized => .AccountAlreadyInitialized
  | .UninitializedAccount => .UninitializedAccount
  | .NotEnoughAccountKeys => .NotEnoughAccountKeys
  | .AccountBorrowFailed => .AccountBorrowFailed
  | .MaxSeedLengthExceeded => .MaxSeedLengthExceeded
  | .InvalidSeeds => .InvalidSeeds
  | .BorshIoError x => .BorshIoError x
  | .AccountNotRentExempt => .AccountNotRentExempt
  | .UnsupportedSysvar => .UnsupportedSysvar
  | .IllegalOwner => .IllegalOwner
  | .MaxAccountsDataAllocationsExceeded => .MaxAccountsDataAllocationsExceeded
  | .InvalidRealloc => .InvalidRealloc
  | .MaxInstructionTraceLengthExceeded => .MaxInstructionTraceLengthExceeded
  | .BuiltinProgramsMustConsumeComputeUnits => .BuiltinProgramsMustConsumeComputeUnits
  | .InvalidAccountOwner => .InvalidAccountOwner
  | .ArithmeticOverflow => .ArithmeticOverflow
  | .Immutable => .Immutable
  | .IncorrectAuthority => .IncorrectAuthority
theorem meta_left (e : PE) : from_meta (to_meta e) = e := by cases e <;> rfl
theorem meta_right (e : NGL_MetaReference.ProgramError) : to_meta (from_meta e) = e := by cases e <;> rfl
#print axioms meta_left
#print axioms meta_right
def to_mapped : PE → NGL_MapReference.ProgramError
  | .Custom x => .Custom x
  | .InvalidArgument => .InvalidArgument
  | .InvalidInstructionData => .InvalidInstructionData
  | .InvalidAccountData => .InvalidAccountData
  | .AccountDataTooSmall => .AccountDataTooSmall
  | .InsufficientFunds => .InsufficientFunds
  | .IncorrectProgramId => .IncorrectProgramId
  | .MissingRequiredSignature => .MissingRequiredSignature
  | .AccountAlreadyInitialized => .AccountAlreadyInitialized
  | .UninitializedAccount => .UninitializedAccount
  | .NotEnoughAccountKeys => .NotEnoughAccountKeys
  | .AccountBorrowFailed => .AccountBorrowFailed
  | .MaxSeedLengthExceeded => .MaxSeedLengthExceeded
  | .InvalidSeeds => .InvalidSeeds
  | .BorshIoError x => .BorshIoError x
  | .AccountNotRentExempt => .AccountNotRentExempt
  | .UnsupportedSysvar => .UnsupportedSysvar
  | .IllegalOwner => .IllegalOwner
  | .MaxAccountsDataAllocationsExceeded => .MaxAccountsDataAllocationsExceeded
  | .InvalidRealloc => .InvalidRealloc
  | .MaxInstructionTraceLengthExceeded => .MaxInstructionTraceLengthExceeded
  | .BuiltinProgramsMustConsumeComputeUnits => .BuiltinProgramsMustConsumeComputeUnits
  | .InvalidAccountOwner => .InvalidAccountOwner
  | .ArithmeticOverflow => .ArithmeticOverflow
  | .Immutable => .Immutable
  | .IncorrectAuthority => .IncorrectAuthority
def from_mapped : NGL_MapReference.ProgramError → PE
  | .Custom x => .Custom x
  | .InvalidArgument => .InvalidArgument
  | .InvalidInstructionData => .InvalidInstructionData
  | .InvalidAccountData => .InvalidAccountData
  | .AccountDataTooSmall => .AccountDataTooSmall
  | .InsufficientFunds => .InsufficientFunds
  | .IncorrectProgramId => .IncorrectProgramId
  | .MissingRequiredSignature => .MissingRequiredSignature
  | .AccountAlreadyInitialized => .AccountAlreadyInitialized
  | .UninitializedAccount => .UninitializedAccount
  | .NotEnoughAccountKeys => .NotEnoughAccountKeys
  | .AccountBorrowFailed => .AccountBorrowFailed
  | .MaxSeedLengthExceeded => .MaxSeedLengthExceeded
  | .InvalidSeeds => .InvalidSeeds
  | .BorshIoError x => .BorshIoError x
  | .AccountNotRentExempt => .AccountNotRentExempt
  | .UnsupportedSysvar => .UnsupportedSysvar
  | .IllegalOwner => .IllegalOwner
  | .MaxAccountsDataAllocationsExceeded => .MaxAccountsDataAllocationsExceeded
  | .InvalidRealloc => .InvalidRealloc
  | .MaxInstructionTraceLengthExceeded => .MaxInstructionTraceLengthExceeded
  | .BuiltinProgramsMustConsumeComputeUnits => .BuiltinProgramsMustConsumeComputeUnits
  | .InvalidAccountOwner => .InvalidAccountOwner
  | .ArithmeticOverflow => .ArithmeticOverflow
  | .Immutable => .Immutable
  | .IncorrectAuthority => .IncorrectAuthority
theorem mapped_left (e : PE) : from_mapped (to_mapped e) = e := by cases e <;> rfl
theorem mapped_right (e : NGL_MapReference.ProgramError) : to_mapped (from_mapped e) = e := by cases e <;> rfl
#print axioms mapped_left
#print axioms mapped_right
end NGL_ErrorCarrier
