import R1Z.PV_RunJoin_RoundAccumulation44
import R1Z.PV_RunJoin_RoundScaleValue44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundResult44
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48 ProverCommitMix48 ProverCommitRoundLoop48
open PV_RunJoin_WideArithmetic44
open PV_RunJoin_FoldCell44 (array)
variable [ExternalTypes]

theorem complete (ops : ExternalFuns) (count : Usize) (small : count.val / 4 ≤ 256)
    (q w : Nat → Raw) (hq : ∀ k, k < 1024 → canonical (q k))
    (hw : ∀ k, k < 1024 → canonical (w k)) :
    ∃ ys : Nat → Raw,
      @prover.round _ (ProverRwP6BodyCandidate.selected ops)
        (Array.to_slice (array count q)) (Array.to_slice (array count w)) = .ok (array 7#usize ys) ∧
      (∀ k, k < 7 → canonical (ys k)) ∧
      ∀ k, k < 7 → value (ys k) = terms q w (ProverCommitRoundOutput48.indices (count.val / 4)) k *
        ProverCommitWideScalar48.factor 536870912#u32 := by
  obtain ⟨xs,hxs,hcxs,hdxs⟩ := PV_RunJoin_RoundAccumulation44.complete ops count small q w hq hw
  refine ⟨fun k => PV_RunJoin_RoundScaleValue44.product (xs k),?_,?_,?_⟩
  · have lengths : Slice.len (Array.to_slice (array count q)) = Slice.len (Array.to_slice (array count w)) := by
      apply UScalar.eq_of_val_eq
      change (Array.to_slice (array count q)).length = (Array.to_slice (array count w)).length
      rw [Array.length_to_slice,Array.length_to_slice]
    unfold prover.round
    simp only [lengths,massert,↓reduceIte,bind_tc_ok]
    have zero : @aspis_core.field.wide_exact.WideExact.ZERO _ (ProverRwP6BodyCandidate.selected ops) =
        .ok (current AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO) := rfl
    rw [zero]
    simp only [bind_tc_ok,hxs]
    exact PV_RunJoin_RoundScaleValue44.complete ops xs
  · intro k hk
    exact ProverCommitWideScalar48.product_canonical _ _
  · intro k hk
    change value (ProverCommitWideScalar48.product (xs k) 536870912#u32) = _
    rw [ProverCommitWideScalar48.product_value,hdxs k hk]
#print axioms complete
end R1Z.PV_RunJoin_RoundResult44
