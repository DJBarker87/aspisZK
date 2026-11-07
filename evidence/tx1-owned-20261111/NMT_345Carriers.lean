import NMT_345Context
import NHJ_DistinctPacket
import NHJ_CheckpointPacket
import NFU_AdapterGetters
import NFU_ZeroPort
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
abbrev OldPE := AdapterRw.solana_program_error.ProgramError
abbrev OldAccount := AdapterRw.r1_pool_adapter.owned.OwnedAccount
def toPE : PE → OldPE
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
def fromPE : OldPE → PE
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
@[simp] theorem from_toPE (e : PE) : fromPE (toPE e) = e := by cases e <;> rfl
@[simp] theorem to_fromPE (e : OldPE) : toPE (fromPE e) = e := by cases e <;> rfl

def mapCore {A B E F : Type} (f : A → B) (g : E → F) : core.result.Result A E → core.result.Result B F
 | .Ok a => .Ok (f a)
 | .Err e => .Err (g e)
def mapOuter {A B : Type} (f : A → B) : Result A → Result B
 | .ok a => .ok (f a)
 | .fail e => .fail e
 | .div => .div

def toAccount (a : Account) : OldAccount :=
 ⟨a.key,a.owner,a.is_signer,a.is_writable,a.executable,
 mapCore id toPE a.length,mapCore id toPE a.bytes⟩
def fromAccount (a : OldAccount) : Account :=
 ⟨a.key,a.owner,a.is_signer,a.is_writable,a.executable,
 mapCore id fromPE a.length,mapCore id fromPE a.bytes⟩
@[simp] theorem account_inverse (a : Account) : fromAccount (toAccount a) = a := by
 cases a with
 | mk k o s w e l b => cases l <;> cases b <;> simp [toAccount,fromAccount,mapCore]
@[simp] theorem old_account_inverse (a : OldAccount) : toAccount (fromAccount a) = a := by
 cases a with
 | mk k o s w e l b => cases l <;> cases b <;> simp [toAccount,fromAccount,mapCore]

def oldArray {N : Usize} (a : Array Account N) : Array OldAccount N :=
 ⟨a.val.map toAccount, by simpa using a.property⟩
#print axioms from_toPE
#print axioms to_fromPE
#print axioms account_inverse
#print axioms old_account_inverse
end NMT_345
