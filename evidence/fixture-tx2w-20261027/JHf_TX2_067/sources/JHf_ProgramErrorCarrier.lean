import JHf_Carrier14
set_option autoImplicit false
namespace AspisR1.JHf_ProgramErrorCarrier
open Aeneas Aeneas.Std Result
def toRaw (e : AdapterRw.solana_program_error.ProgramError) : AspisR1AdapterReconstruct.solana_program_error.ProgramError :=
  match e with
  | .Custom v=>.Custom v
  | .InvalidArgument=>.InvalidArgument
  | .InvalidInstructionData=>.InvalidInstructionData
  | .InvalidAccountData=>.InvalidAccountData
  | .AccountDataTooSmall=>.AccountDataTooSmall
  | .InsufficientFunds=>.InsufficientFunds
  | .IncorrectProgramId=>.IncorrectProgramId
  | .MissingRequiredSignature=>.MissingRequiredSignature
  | .AccountAlreadyInitialized=>.AccountAlreadyInitialized
  | .UninitializedAccount=>.UninitializedAccount
  | .NotEnoughAccountKeys=>.NotEnoughAccountKeys
  | .AccountBorrowFailed=>.AccountBorrowFailed
  | .MaxSeedLengthExceeded=>.MaxSeedLengthExceeded
  | .InvalidSeeds=>.InvalidSeeds
  | .BorshIoError v=>.BorshIoError v
  | .AccountNotRentExempt=>.AccountNotRentExempt
  | .UnsupportedSysvar=>.UnsupportedSysvar
  | .IllegalOwner=>.IllegalOwner
  | .MaxAccountsDataAllocationsExceeded=>.MaxAccountsDataAllocationsExceeded
  | .InvalidRealloc=>.InvalidRealloc
  | .MaxInstructionTraceLengthExceeded=>.MaxInstructionTraceLengthExceeded
  | .BuiltinProgramsMustConsumeComputeUnits=>.BuiltinProgramsMustConsumeComputeUnits
  | .InvalidAccountOwner=>.InvalidAccountOwner
  | .ArithmeticOverflow=>.ArithmeticOverflow
  | .Immutable=>.Immutable
  | .IncorrectAuthority=>.IncorrectAuthority
def fromRaw (e : AspisR1AdapterReconstruct.solana_program_error.ProgramError) : AdapterRw.solana_program_error.ProgramError :=
  match e with
  | .Custom v=>.Custom v
  | .InvalidArgument=>.InvalidArgument
  | .InvalidInstructionData=>.InvalidInstructionData
  | .InvalidAccountData=>.InvalidAccountData
  | .AccountDataTooSmall=>.AccountDataTooSmall
  | .InsufficientFunds=>.InsufficientFunds
  | .IncorrectProgramId=>.IncorrectProgramId
  | .MissingRequiredSignature=>.MissingRequiredSignature
  | .AccountAlreadyInitialized=>.AccountAlreadyInitialized
  | .UninitializedAccount=>.UninitializedAccount
  | .NotEnoughAccountKeys=>.NotEnoughAccountKeys
  | .AccountBorrowFailed=>.AccountBorrowFailed
  | .MaxSeedLengthExceeded=>.MaxSeedLengthExceeded
  | .InvalidSeeds=>.InvalidSeeds
  | .BorshIoError v=>.BorshIoError v
  | .AccountNotRentExempt=>.AccountNotRentExempt
  | .UnsupportedSysvar=>.UnsupportedSysvar
  | .IllegalOwner=>.IllegalOwner
  | .MaxAccountsDataAllocationsExceeded=>.MaxAccountsDataAllocationsExceeded
  | .InvalidRealloc=>.InvalidRealloc
  | .MaxInstructionTraceLengthExceeded=>.MaxInstructionTraceLengthExceeded
  | .BuiltinProgramsMustConsumeComputeUnits=>.BuiltinProgramsMustConsumeComputeUnits
  | .InvalidAccountOwner=>.InvalidAccountOwner
  | .ArithmeticOverflow=>.ArithmeticOverflow
  | .Immutable=>.Immutable
  | .IncorrectAuthority=>.IncorrectAuthority
theorem from_to (e : AdapterRw.solana_program_error.ProgramError) : fromRaw (toRaw e)=e := by
  cases e <;> rfl
#print axioms from_to

theorem to_from (e : AspisR1AdapterReconstruct.solana_program_error.ProgramError) : toRaw (fromRaw e)=e := by
  cases e <;> rfl
#print axioms to_from
end AspisR1.JHf_ProgramErrorCarrier
