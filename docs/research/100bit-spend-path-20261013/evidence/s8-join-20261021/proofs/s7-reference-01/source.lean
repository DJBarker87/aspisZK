import S8JoinModelRepresentation
import S7JoinAccumulatorReference

/-! Consume the committed sibling S7 reference, without editing its modules.
The upstream revision/source/receipt is pinned in upstream-s7.json. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S8JoinS7Reference
attribute [local instance] Classical.propDecidable
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase
open S8OwnedP6Finish S8JoinFinishField S8JoinAccumulatorStage S8JoinModelRepresentation

/-- This state is produced by S7's field reference, not supplied as sums. -/
def reached (data : Data) (q : Queries) (rho : QM31Exact) :=
  S7JoinAccumulatorReference.run LiteralOpeningView.eK data q rho

theorem weights_eq (data : Data) (q : Queries) (rho : QM31Exact) :
    (reached data q rho).weights=weight q rho := by
  funext l
  unfold reached
  rw [S7JoinAccumulatorReference.run_eq]
  exact QueryAccumulator.run22_weights _ _ _ _ l

/-- All old P6 finish conditions follow at the canonical realization of S7's
produced state. Source/checkpoint provenance is not encoded by this realization. -/
theorem reached_caller (data : Data) (q : Queries) (rho : QM31Exact) :
    S8Kani2CallerJoin.CallerInvariant (raw (reached data q rho).weights) old
      (fun j k => if h:j<64 then (limb ((reached data q rho).weights ⟨j,h⟩) k).val else 0) :=
  model_caller _

/-- S7's whole field reference followed by the emitted S8 finish has the
exact frozen ClosedSum Boolean on every input, including arithmetic rejection. -/
theorem finish_check (data : Data) (q : Queries) (rho : QM31Exact) :
    ∃ out : Weights,
      S8OwnedP6.finish_owned (raw (reached data q rho).weights) old=.ok out ∧
      check out data q rho =
        decide (HchecksAccumulator.ClosedSum LiteralOpeningView.eK data q rho) := by
  rw [weights_eq]
  exact model_finish_check data q rho

/-- The mutable finish also realizes every reached S7 field-reference weight. -/
theorem mutable_finish (data : Data) (q : Queries) (rho : QM31Exact) (terms : Usize) :
    ∃ out : S8Kani2MutableExtraction.batched_weights.FinishSlice,
      S8Kani2MutableExtraction.batched_weights.BatchedWeights.finish
        (⟨raw (reached data q rho).weights,terms⟩ : S8Kani2MutableValue.F.BW)
        (S8Kani2FinishReferenceJoin.toSlice old)=.ok out ∧
      out.val.map mutableField=List.ofFn (reached data q rho).weights := by
  obtain ⟨out,run,cells⟩ := mutable_field (raw (reached data q rho).weights) old terms
    (by simp [raw,old])
  refine ⟨out,run,?_⟩
  rw [cells]
  simp [raw,old,List.map_ofFn,Function.comp_def,row_field]

#print axioms weights_eq
#print axioms reached_caller
#print axioms finish_check
#print axioms mutable_finish
end AspisR1.S8JoinS7Reference
end
