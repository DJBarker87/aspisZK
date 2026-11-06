import PCA_Event
set_option autoImplicit false
namespace PCC
/-- Full pinned SDK value is retained at inspection sites; quotient only at ABI observation. -/
inductive ProgramError where
  | Custom (code : UInt32)
  | InvalidArgument
  | InvalidInstructionData
  | InvalidAccountData
  | AccountDataTooSmall
  | InsufficientFunds
  | IncorrectProgramId
  | MissingRequiredSignature
  | AccountAlreadyInitialized
  | UninitializedAccount
  | NotEnoughAccountKeys
  | AccountBorrowFailed
  | MaxSeedLengthExceeded
  | InvalidSeeds
  | BorshIoError (message : String)
  | AccountNotRentExempt
  | UnsupportedSysvar
  | IllegalOwner
  | MaxAccountsDataAllocationsExceeded
  | InvalidRealloc
  | MaxInstructionTraceLengthExceeded
  | BuiltinProgramsMustConsumeComputeUnits
  | InvalidAccountOwner
  | ArithmeticOverflow
  | Immutable
  | IncorrectAuthority
  deriving DecidableEq

/-- Transcription: solana-program-error 2.2.2 From<ProgramError> for u64. -/
def ProgramError.abi : ProgramError → UInt64
  | .Custom code => if code = 0 then 4294967296 else UInt64.ofNat code.toNat
  | .InvalidArgument => 8589934592
  | .InvalidInstructionData => 12884901888
  | .InvalidAccountData => 17179869184
  | .AccountDataTooSmall => 21474836480
  | .InsufficientFunds => 25769803776
  | .IncorrectProgramId => 30064771072
  | .MissingRequiredSignature => 34359738368
  | .AccountAlreadyInitialized => 38654705664
  | .UninitializedAccount => 42949672960
  | .NotEnoughAccountKeys => 47244640256
  | .AccountBorrowFailed => 51539607552
  | .MaxSeedLengthExceeded => 55834574848
  | .InvalidSeeds => 60129542144
  | .BorshIoError _ => 64424509440
  | .AccountNotRentExempt => 68719476736
  | .UnsupportedSysvar => 73014444032
  | .IllegalOwner => 77309411328
  | .MaxAccountsDataAllocationsExceeded => 81604378624
  | .InvalidRealloc => 85899345920
  | .MaxInstructionTraceLengthExceeded => 90194313216
  | .BuiltinProgramsMustConsumeComputeUnits => 94489280512
  | .InvalidAccountOwner => 98784247808
  | .ArithmeticOverflow => 103079215104
  | .Immutable => 107374182400
  | .IncorrectAuthority => 111669149696

/-- Entrypoint 2.3.0 macro: no payload logging or formatting on Err. -/
def entrypoint (reply : Except ProgramError Unit) : UInt64 :=
  match reply with
  | .ok () => 0
  | .error e => e.abi

/-- This relation preserves the full Result tag; it never identifies Ok with Err. -/
def AbiRelated {α : Type} (x y : Except ProgramError α) : Prop :=
  match x, y with
  | .ok a, .ok b => a = b
  | .error e, .error f => e.abi = f.abi
  | _, _ => False

theorem entrypoint_error (e : ProgramError) : entrypoint (.error e) = e.abi := rfl
theorem borsh_payload_abi (x y : String) :
    (ProgramError.BorshIoError x).abi = (ProgramError.BorshIoError y).abi := rfl
#print axioms entrypoint_error
#print axioms borsh_payload_abi
end PCC
