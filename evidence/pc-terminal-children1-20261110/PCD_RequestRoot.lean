import PCD_RequestBridge
import PCD_BoxFold
set_option autoImplicit false
noncomputable section
namespace PCD_RequestRoot
open Aeneas Aeneas.Std PCD_Request PCD_FrozenRequest

/-- Full emitted ProgramError carrier. The final wrapper's reachable subset is
proved by its emitted Result, rather than obtained by an ABI quotient. -/
def mapProgramError : solana_program_error.PCD_ProgramError → PCD.ProgramError
  | .Custom code => .custom (UInt32.ofNat code.val)
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
  | .BorshIoError message => .borshIoError message
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

def observe : Result (core.result.Result LocalRequest solana_program_error.PCD_ProgramError) → PCD.Exit Request
  | .ok (.Ok value) => .ok (unmapRequest value)
  | .ok (.Err error) => .error (mapProgramError error)
  | .fail _ => .abort
  | .div => .diverge

def attachAllocation (allocation : Allocation) : PCD.Exit Request → PCD.Exit (Owned Request)
  | .ok value => match allocation with
    | .aborted => .abort
    | .returned block => .ok ⟨block,value⟩
  | .error error => .error error
  | .abort => .abort
  | .diverge => .diverge

/-- Whole own-input model with complete child/allocator event prefixes. The
allocation observation is the existing named Allocator item, not a new runtime
law or a successful-allocation premise. Native source cuts remain separate. -/
noncomputable def RowSpec_POOL_314 (bytes : Slice U8) (allocation : Allocation) :=
  PCD_BoxFold.specification bytes allocation

theorem result_state_effects {State : Type} (bytes : Slice U8) (allocation : Allocation) (state : State) :
    (PCD_BoxFold.source bytes allocation,state) = (RowSpec_POOL_314 bytes allocation,state) :=
  PCD_BoxFold.result_state_effects bytes allocation state

/-- The emitted ACTUAL parent and safe extracted reference have exactly the
same final Result projection, including every child Err and allocator abort.
The trace theorem above additionally retains the original child error payload. -/
theorem emitted_reply (bytes : Slice U8) (allocation : Allocation) :
    attachAllocation allocation (observe (pair_forest.decode_terminal_request_box_v1 bytes)) =
      (PCD_BoxFold.source bytes allocation).reply := by
  rw [PCD_RequestEmitter.emitted_complete]
  unfold PCD_RequestEmitter.continuation PCD_BoxFold.source
  cases h : NFY_NFD_RequestOracle.runSlice bytes with
  | fail error => rfl
  | div => rfl
  | ok decoded =>
    cases decoded with
    | Err error => rfl
    | Ok value =>
      change attachAllocation allocation (.ok (unmapRequest (mapRequest value))) =
        (PCD_BoxFold.fold bytes allocation (.ok (.Ok value))).reply
      rw [request_roundtrip]
      cases allocation <;> rfl
#print axioms result_state_effects
#print axioms emitted_reply
end PCD_RequestRoot
