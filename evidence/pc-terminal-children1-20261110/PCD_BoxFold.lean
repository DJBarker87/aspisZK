import PCD_Request
set_option autoImplicit false
noncomputable section
namespace PCD_BoxFold
open Aeneas Aeneas.Std PCD_Request

/-- Private allocation events are retained. An allocator abort is never a
recoverable ProgramError. Runtime/allocator trust is NOT discharged here. -/
inductive Event (Input Value Error : Type) where
  | childCall (input : Input)
  | childReturned (reply : core.result.Result Value Error)
  | allocationAttempt (value : Value)
  | allocationReturned (block : Nat) (value : Value)
structure Execution (Input Value Error : Type) where
  reply : PCD.Exit (Owned Value)
  events : List (Event Input Value Error)

def fold {Input Value Error : Type} (input : Input) (allocation : Allocation)
    (decoded : Result (core.result.Result Value Error)) : Execution Input Value Error :=
  match decoded with
  | .fail _ => ⟨.abort,[.childCall input]⟩
  | .div => ⟨.diverge,[.childCall input]⟩
  | .ok (.Err error) => ⟨.error .invalidInstructionData,
      [.childCall input,.childReturned (.Err error)]⟩
  | .ok (.Ok value) => match allocation with
    | .aborted => ⟨.abort,[.childCall input,.childReturned (.Ok value),.allocationAttempt value]⟩
    | .returned block => ⟨.ok ⟨block,value⟩,
        [.childCall input,.childReturned (.Ok value),.allocationAttempt value,.allocationReturned block value]⟩

/-- Generic allocation/error fold; not a row root with an unknown child. -/
theorem reply_exact {Input Value Error : Type} (input : Input) (allocation : Allocation)
    (decoded : Result (core.result.Result Value Error)) :
    (fold input allocation decoded).reply = wrapReply allocation decoded := by
  cases decoded with
  | fail error => rfl
  | div => rfl
  | ok decoded => cases decoded with
    | Err error => rfl
    | Ok value => cases allocation <;> rfl

theorem error_prefix {Input Value Error : Type} (input : Input) (allocation : Allocation) (error : Error) :
    (fold (Value:=Value) input allocation (.ok (.Err error))).events =
      [.childCall input,.childReturned (.Err error)] := rfl

theorem abort_prefix {Input Value Error : Type} (input : Input) (value : Value) :
    fold (Error:=Error) input .aborted (.ok (.Ok value)) =
      ⟨.abort,[.childCall input,.childReturned (.Ok value),.allocationAttempt value]⟩ := rfl

abbrev RequestError := AspisR1.NFY_JHd_RequestNative.FormatError
noncomputable def source (bytes : Slice U8) (allocation : Allocation) :
    Execution (Slice U8) Request RequestError :=
  fold bytes allocation (NFY_NFD_RequestOracle.runSlice bytes)
noncomputable def specification (bytes : Slice U8) (allocation : Allocation) :
    Execution (Slice U8) Request RequestError :=
  fold bytes allocation (AspisR1.NFY_JHd_RequestNative.decode bytes)

/-- Concrete SAME-call decoder substitution: arbitrary own input slices,
complete Result, no success/length/endpoint assumption, exact abort prefixes. -/
theorem result_state_effects {State : Type} (bytes : Slice U8) (allocation : Allocation) (state : State) :
    (source bytes allocation,state) = (specification bytes allocation,state) := by
  have same : NFY_NFD_RequestOracle.runSlice bytes = AspisR1.NFY_JHd_RequestNative.decode bytes :=
    congrArg Prod.fst (NFY_NFD_RequestOracle.result_state_effects bytes state)
  unfold source specification
  rw [same]
#print axioms reply_exact
#print axioms error_prefix
#print axioms abort_prefix
#print axioms result_state_effects
end PCD_BoxFold
