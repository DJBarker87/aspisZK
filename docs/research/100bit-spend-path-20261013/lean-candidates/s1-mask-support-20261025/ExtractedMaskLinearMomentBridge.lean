import Lean.Elab.Tactic.Omega
import ExtractedMaskLinearRecurrence
import ExtractedMaskLinearLoop

/-! A pure bridge from the executable-shaped Nat recurrence used by the
selected-mask loop model to the retained reverse accumulator relation.
This module has no Rust/source-refinement claim. -/
set_option autoImplicit false

namespace AspisR1.ExtractedMaskLinearMomentBridge

abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact

open AspisR1.ExtractedMaskLinearRecurrence
open AspisR1.ExtractedMaskLinearLoop

def pointOf (α : Fin 10 → ExactQM) : Nat → ExactQM := fun i =>
  if h : i < 10 then α ⟨i, h⟩ else 0

/-- Running the model for the remaining `n` coordinates transforms a state
at boundary `n` into the boundary-zero state described by the existing
`ReverseAccumulator` relation. The skip at absolute coordinate zero is the
same branch as `ReverseAccumulator.step`. -/
theorem accumulatorModel_preserves_reverse (α : Fin 10 → ExactQM) :
    ∀ n, n ≤ 10 → ∀ suffix weighted,
      ReverseAccumulator α n suffix weighted →
      ∃ out : ExactQM × ExactQM,
        accumulatorModel (pointOf α) n (suffix, weighted) = out ∧
        ReverseAccumulator α 0 out.1 out.2 := by
  intro n
  induction n with
  | zero =>
      intro hn suffix weighted h
      refine ⟨(suffix, weighted), ?_, h⟩
      rfl
  | succ n ih =>
      intro hn suffix weighted h
      have hnlt : n < 10 := by omega
      let suffix1 := suffix + α ⟨n, hnlt⟩
      let weighted1 := if n = 0 then weighted else weighted + suffix1
      have hnext : ReverseAccumulator α n suffix1 weighted1 := by
        simpa [suffix1, weighted1] using
          (ReverseAccumulator.step (α := α) (k := n) hnlt h)
      obtain ⟨out, hmodel, hfinal⟩ := ih (by omega) suffix1 weighted1 hnext
      refine ⟨out, ?_, hfinal⟩
      simpa [accumulatorModel, pointOf, hnlt, suffix1, weighted1] using hmodel

/-- The zero-seeded ten-coordinate model yields the two selected linear
forms by reusing the existing reverse-accumulator moment theorem. -/
theorem selected_outputs_of_accumulatorModel (α : Fin 10 → ExactQM) :
    let out := accumulatorModel (pointOf α) 10 (0, 0)
    (3 : ExactQM) * out.1 + 22 * out.2 = maskLinear 0 α ∧
    (275 : ExactQM) * out.1 + 150 * out.2 = maskLinear 16 α := by
  dsimp
  obtain ⟨out, hmodel, hfinal⟩ :=
    accumulatorModel_preserves_reverse α 10 (by omega) 0 0
      ReverseAccumulator.finished
  have hselected := reverseAccumulator_selected_outputs α hfinal
  rw [← hmodel] at hselected
  exact hselected

#print axioms AspisR1.ExtractedMaskLinearMomentBridge.accumulatorModel_preserves_reverse
#print axioms AspisR1.ExtractedMaskLinearMomentBridge.selected_outputs_of_accumulatorModel

end AspisR1.ExtractedMaskLinearMomentBridge
