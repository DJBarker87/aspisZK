import NNG_Carriers328
import NMT_345RSLCarriers
set_option autoImplicit false
namespace AspisR1.NNG_PE345
open Aeneas Aeneas.Std
-- Exact nominal enum transport; every ProgramError payload is preserved.
def fromFirst : NMT_first.solana_program_error.ProgramError → NMT_345.PE
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

theorem source (e : NMT_first.solana_program_error.ProgramError) :
 NMT_345.pe (fromFirst e)=NNG_Carriers328.pe e := by cases e <;> rfl
#print axioms source
end AspisR1.NNG_PE345
