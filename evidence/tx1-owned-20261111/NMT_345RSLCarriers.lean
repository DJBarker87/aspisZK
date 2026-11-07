import NMT_345Carriers
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result

def byte (x : U8) : UInt8 := UInt8.ofNat x.val
theorem byte_nat (x : U8) : (byte x).toNat = x.val := by
 have bound : x.val < 256 := x.hmax
 change x.val % 256 = x.val
 exact Nat.mod_eq_of_lt (by omega)
theorem byte_injective : Function.Injective byte := by
 intro x y h
 apply UScalar.eq_of_val_eq
 have e := congrArg UInt8.toNat h
 simpa only [byte_nat] using e

def key (x : Key) : RSL.B32 := ⟨x.val.map byte, by simpa using x.property⟩
theorem key_injective : Function.Injective key := by
 intro x y h
 have e := congrArg RSL.B32.bytes h
 have vals : x.val = y.val := List.map_injective_iff.mpr byte_injective e
 exact Subtype.ext vals

def pe : PE → RSL.ProgramError
 | .Custom x => .custom (UInt32.ofNat x.val)
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

def rustResult {A B : Type} (f : A → B) : core.result.Result A PE → Except RSL.ProgramError B
 | .Ok a => .ok (f a)
 | .Err e => .error (pe e)
def account (x : Account) : RSL.OwnedAccount :=
 ⟨key x.key,key x.owner,x.is_signer,x.is_writable,x.executable,
 rustResult (fun n => n.val) x.length,
 rustResult (fun b => b.val.map byte) x.bytes⟩
#print axioms byte_nat
#print axioms byte_injective
#print axioms key_injective
end NMT_345
