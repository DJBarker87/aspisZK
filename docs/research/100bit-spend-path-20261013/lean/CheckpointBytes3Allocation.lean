import CheckpointBytes3Namespaces
import OraclePortStdAllocation

set_option autoImplicit false
namespace AspisR1.CheckpointBytes3Allocation
open Aeneas Aeneas.Std Result
open AspisR1Stage2

/-- Reservation outcome is an execution input, not an availability theorem.
The typed source Error is retained, together with all successful Vec content. -/
def filled (reserved : Bool) (n : Usize) (value : aspis_core.field.QM31) :
    Result (core.result.Result (alloc.vec.Vec aspis_core.field.QM31) verifier.Error) := do
  let out ← OraclePortStdAllocation.filled n value reserved
  match out with
  | .error _ => ok (.Err .Allocation)
  | .ok v => ok (.Ok v)

theorem filled_exact (reserved : Bool) (n : Usize) (value : aspis_core.field.QM31) :
    filled reserved n value =
      if reserved then ok (.Ok ⟨List.replicate n.val value,by simp; scalar_tac⟩)
      else ok (.Err .Allocation) := by
  cases reserved <;>
    simp [filled,OraclePortStdAllocation.filled_exact,OraclePortStdAllocation.filledSpec]

theorem filled_success_content (reserved : Bool) (n : Usize) (value : aspis_core.field.QM31)
    (out : alloc.vec.Vec aspis_core.field.QM31)
    (success : filled reserved n value = ok (.Ok out)) :
    reserved = true ∧ out.val = List.replicate n.val value := by
  rw [filled_exact] at success
  cases reserved with
  | false => cases success
  | true =>
    have eq := core.result.Result.Ok.inj (Result.ok.inj success)
    exact ⟨rfl,(congrArg Subtype.val eq).symm⟩

theorem filled_rejection (n : Usize) (value : aspis_core.field.QM31) :
    filled false n value = ok (.Err verifier.Error.Allocation) := rfl

/-- A total all-reservation successful bridge would assert a false premise.
Success-conditioned source adoption can instead derive the reservation fact. -/
theorem no_unconditional_allocation_success (n : Usize) (value : aspis_core.field.QM31) :
    ¬ ∀ reserved, ∃ out, filled reserved n value = ok (.Ok out) := by
  intro h
  obtain ⟨out,success⟩ := h false
  cases success

#print axioms filled_exact
#print axioms filled_success_content
#print axioms filled_rejection
#print axioms no_unconditional_allocation_success
end AspisR1.CheckpointBytes3Allocation
