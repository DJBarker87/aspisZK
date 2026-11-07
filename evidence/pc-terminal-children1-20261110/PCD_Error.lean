import Init
set_option autoImplicit false
namespace PCD
/-- Full solana-program-error 2.2.2 algebra, including the String payload.
No ABI quotient is used in row models. This declaration is a draft transcription,
not a native correspondence certificate. -/
inductive ProgramError where
  | custom (code : UInt32)
  | invalidArgument | invalidInstructionData | invalidAccountData
  | accountDataTooSmall | insufficientFunds | incorrectProgramId
  | missingRequiredSignature | accountAlreadyInitialized | uninitializedAccount
  | notEnoughAccountKeys | accountBorrowFailed | maxSeedLengthExceeded
  | invalidSeeds | borshIoError (message : String)
  | accountNotRentExempt | unsupportedSysvar | illegalOwner
  | maxAccountsDataAllocationsExceeded | invalidRealloc
  | maxInstructionTraceLengthExceeded | builtinProgramsMustConsumeComputeUnits
  | invalidAccountOwner | arithmeticOverflow | immutable | incorrectAuthority
  deriving DecidableEq
/-- Inner Err differs from allocation/runtime abort and divergence. -/
inductive Exit (α : Type) where
  | ok (value : α)
  | error (value : ProgramError)
  | abort
  | diverge
  deriving DecidableEq

def mapExit {α β : Type} (f : α → β) : Exit α → Exit β
  | .ok a => .ok (f a)
  | .error e => .error e
  | .abort => .abort
  | .diverge => .diverge

theorem map_error {α β : Type} (f : α → β) (e : ProgramError) :
    mapExit f (.error e) = .error e := rfl

theorem map_abort {α β : Type} (f : α → β) :
    mapExit f .abort = .abort := rfl

theorem payload_preserved (s : String) :
    mapExit (fun x : Unit => x) (.error (.borshIoError s)) =
      .error (.borshIoError s) := rfl
#print axioms map_error
#print axioms map_abort
#print axioms payload_preserved
end PCD
