import NHP_ErrorRef.Funs
import NHC_ErrorMove
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NHP_ErrorModel
abbrev Error := AdapterRw.solana_program_error.ProgramError

def decode (tag : U8) (payload : U32) : Error :=
  match tag.val with
  | 1 => .InvalidArgument
  | 2 => .InvalidInstructionData
  | 3 => .InvalidAccountData
  | 4 => .AccountDataTooSmall
  | 5 => .InsufficientFunds
  | 6 => .IncorrectProgramId
  | 7 => .MissingRequiredSignature
  | 8 => .AccountAlreadyInitialized
  | 9 => .UninitializedAccount
  | 10 => .NotEnoughAccountKeys
  | 11 => .AccountBorrowFailed
  | 12 => .MaxSeedLengthExceeded
  | 13 => .InvalidSeeds
  | 14 => .BorshIoError "Unknown"
  | 15 => .AccountNotRentExempt
  | 16 => .UnsupportedSysvar
  | 17 => .IllegalOwner
  | 18 => .MaxAccountsDataAllocationsExceeded
  | 19 => .InvalidRealloc
  | 20 => .MaxInstructionTraceLengthExceeded
  | 21 => .BuiltinProgramsMustConsumeComputeUnits
  | 22 => .InvalidAccountOwner
  | 23 => .ArithmeticOverflow
  | 24 => .Immutable
  | 25 => .IncorrectAuthority
  | _ => .Custom payload

def encode : Error → U8 × U32
  | .Custom value => (0#u8, value)
  | .InvalidArgument => (1#u8, 0#u32)
  | .InvalidInstructionData => (2#u8, 0#u32)
  | .InvalidAccountData => (3#u8, 0#u32)
  | .AccountDataTooSmall => (4#u8, 0#u32)
  | .InsufficientFunds => (5#u8, 0#u32)
  | .IncorrectProgramId => (6#u8, 0#u32)
  | .MissingRequiredSignature => (7#u8, 0#u32)
  | .AccountAlreadyInitialized => (8#u8, 0#u32)
  | .UninitializedAccount => (9#u8, 0#u32)
  | .NotEnoughAccountKeys => (10#u8, 0#u32)
  | .AccountBorrowFailed => (11#u8, 0#u32)
  | .MaxSeedLengthExceeded => (12#u8, 0#u32)
  | .InvalidSeeds => (13#u8, 0#u32)
  | .BorshIoError _ => (14#u8, 0#u32)
  | .AccountNotRentExempt => (15#u8, 0#u32)
  | .UnsupportedSysvar => (16#u8, 0#u32)
  | .IllegalOwner => (17#u8, 0#u32)
  | .MaxAccountsDataAllocationsExceeded => (18#u8, 0#u32)
  | .InvalidRealloc => (19#u8, 0#u32)
  | .MaxInstructionTraceLengthExceeded => (20#u8, 0#u32)
  | .BuiltinProgramsMustConsumeComputeUnits => (21#u8, 0#u32)
  | .InvalidAccountOwner => (22#u8, 0#u32)
  | .ArithmeticOverflow => (23#u8, 0#u32)
  | .Immutable => (24#u8, 0#u32)
  | .IncorrectAuthority => (25#u8, 0#u32)

def Known : Error → Prop
  | .BorshIoError text => text = "Unknown"
  | _ => True

theorem decoded_known (tag : U8) (payload : U32) : Known (decode tag payload) := by
  unfold decode
  split <;> simp [Known]
#print axioms decoded_known

theorem decode_encode (error : Error) (h : Known error) :
    decode (encode error).1 (encode error).2 = error := by
  cases error <;> simp_all [decode,encode,Known]
#print axioms decode_encode

theorem classifier_total (word : U64) :
    ∃ pair, NHP_ErrorRef.NHP_error_reference.classify word = ok pair := by
  unfold NHP_ErrorRef.NHP_error_reference.classify
  split <;> exact ⟨_, rfl⟩
#print axioms classifier_total

def result (word : U64) : Result Error := do
  let pair ← NHP_ErrorRef.NHP_error_reference.classify word
  ok (decode pair.1 pair.2)

theorem result_domain (word : U64) : ∃ error, result word = ok error ∧ Known error := by
  obtain ⟨pair,h⟩ := classifier_total word
  exact ⟨decode pair.1 pair.2, by simp [result,h], decoded_known _ _⟩
#print axioms result_domain

theorem unknown_utf8 : "Unknown".toUTF8.data = #[85,110,107,110,111,119,110] := by decide
#print axioms unknown_utf8
end NHP_ErrorModel
