import AdapterRwModel
import RSL_Base
set_option autoImplicit false
namespace NND_Carrier
open Aeneas Aeneas.Std AdapterRw

def byte (x : U8) : UInt8 := UInt8.ofBitVec x.bv
def unbyte (x : UInt8) : U8 := ⟨x.toBitVec⟩
def word (x : U32) : UInt32 := UInt32.ofBitVec x.bv
def unword (x : UInt32) : U32 := ⟨x.toBitVec⟩
def slot (x : U64) : UInt64 := UInt64.ofBitVec x.bv
def unslot (x : UInt64) : U64 := ⟨x.toBitVec⟩
@[simp] theorem byte_back (x : U8) : unbyte (byte x) = x := by cases x; rfl
@[simp] theorem byte_forth (x : UInt8) : byte (unbyte x) = x := by cases x; rfl
@[simp] theorem word_back (x : U32) : unword (word x) = x := by cases x; rfl
@[simp] theorem word_forth (x : UInt32) : word (unword x) = x := by cases x; rfl
@[simp] theorem slot_back (x : U64) : unslot (slot x) = x := by cases x; rfl
@[simp] theorem slot_forth (x : UInt64) : slot (unslot x) = x := by cases x; rfl

def bytes (x : Slice U8) : RSL.Bytes := x.val.map byte
def key (x : Array U8 32#usize) : RSL.B32 :=
 ⟨x.val.map byte, by simpa using x.property⟩
def unkey (x : RSL.B32) : Array U8 32#usize :=
 ⟨x.bytes.map unbyte, by simpa using x.len⟩
@[simp] theorem bytes_length (x : Slice U8) : (bytes x).length = x.val.length := by simp [bytes]
@[simp] theorem key_back (x : Array U8 32#usize) : unkey (key x) = x := by
 cases x
 simp [unkey,key,List.map_map,Function.comp_def]
@[simp] theorem key_forth (x : RSL.B32) : key (unkey x) = x := by
 cases x
 simp [key,unkey,List.map_map,Function.comp_def]

def error : solana_program_error.ProgramError → RSL.ProgramError
 | .Custom c => .custom (word c)
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
 | .BorshIoError s => .borshIoError s
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

def unerror : RSL.ProgramError → solana_program_error.ProgramError
 | .custom c => .Custom (unword c)
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
 | .borshIoError s => .BorshIoError s
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

@[simp] theorem error_back (x : solana_program_error.ProgramError) : unerror (error x) = x := by
 cases x <;> simp [error,unerror]
@[simp] theorem error_forth (x : RSL.ProgramError) : error (unerror x) = x := by
 cases x <;> simp [error,unerror]

def reply {A B : Type} (f : A → B) : core.result.Result A solana_program_error.ProgramError → Except RSL.ProgramError B
 | .Ok x => .ok (f x)
 | .Err e => .error (error e)
def unreply {A B : Type} (f : B → A) : Except RSL.ProgramError B → core.result.Result A solana_program_error.ProgramError
 | .ok x => .Ok (f x)
 | .error e => .Err (unerror e)
theorem reply_back {A B : Type} (f : A → B) (g : B → A) (h : ∀ x, g (f x) = x)
 (x : core.result.Result A solana_program_error.ProgramError) : unreply g (reply f x) = x := by
 cases x <;> simp [reply,unreply,h]

#print axioms byte_back
#print axioms byte_forth
#print axioms word_back
#print axioms word_forth
#print axioms slot_back
#print axioms slot_forth
#print axioms bytes_length
#print axioms key_back
#print axioms key_forth
#print axioms error_back
#print axioms error_forth
#print axioms reply_back
end NND_Carrier
