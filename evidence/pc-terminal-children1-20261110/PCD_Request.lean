import NFY_Part059
import PCD_Error
set_option autoImplicit false
namespace PCD_Request
open Aeneas.Std
/-- An observation of the already named allocator trust item. It includes
non-return; no recoverable Rust Err is invented for Box::new. This is an
INTERMEDIATE value/abort fold, not a native allocator or Pool-row certificate. -/
inductive Allocation where
  | returned (block : Nat)
  | aborted
structure Owned (α : Type) where
  block : Nat
  value : α

def wrapReply {α ε : Type} (allocation : Allocation) :
    Aeneas.Result (core.result.Result α ε) → PCD.Exit (Owned α)
  | .ok (.Err _) => .error .invalidInstructionData
  | .ok (.Ok value) => match allocation with
    | .returned block => .ok ⟨block,value⟩
    | .aborted => .abort
  | .fail _ => .abort
  | .div => .diverge

abbrev Request := AspisR1.NFY_JHd_RequestNative.Request
noncomputable def source (bytes : Slice U8) (allocation : Allocation) : PCD.Exit (Owned Request) :=
  wrapReply allocation (NFY_NFD_RequestOracle.runSlice bytes)
noncomputable def specification (bytes : Slice U8) (allocation : Allocation) : PCD.Exit (Owned Request) :=
  wrapReply allocation (AspisR1.NFY_JHd_RequestNative.decode bytes)

/-- Substitution at the SAME arbitrary slice; no length or successful-decoder
premise is imposed. This model-only lemma neither supplies the native forwarding
certificate nor licenses an unconstrained child stub. -/
theorem same_input {State : Type} (bytes : Slice U8) (allocation : Allocation) (state : State) :
    (source bytes allocation,state) = (specification bytes allocation,state) := by
  have same := congrArg Prod.fst (NFY_NFD_RequestOracle.result_state_effects bytes state)
  unfold source specification
  rw [same]

theorem error_before_allocation {α ε : Type} (allocation : Allocation) (error : ε) :
    wrapReply (α:=α) allocation (.ok (.Err error)) = .error .invalidInstructionData := rfl

theorem allocated_value {α ε : Type} (block : Nat) (value : α) :
    wrapReply (ε:=ε) (.returned block) (.ok (.Ok value)) = .ok ⟨block,value⟩ := rfl

theorem allocation_abort {α ε : Type} (value : α) :
    wrapReply (ε:=ε) .aborted (.ok (.Ok value)) = .abort := rfl
#print axioms same_input
#print axioms error_before_allocation
#print axioms allocated_value
#print axioms allocation_abort
end PCD_Request
