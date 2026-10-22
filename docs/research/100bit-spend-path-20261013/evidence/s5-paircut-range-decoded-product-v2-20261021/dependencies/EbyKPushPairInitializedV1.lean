import EbyKPushPairForwardStateV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S5EbyKPushPairInitializedV1

open AspisR1WeightsPairCutEbyKDotOpsV1
open AspisR1S5EbyKConcreteOpsInstanceV1
open AspisR1S5EbyKPushPairForwardStateV1

local instance installedOps : AspisR1WeightsPairCut.fast_pairing.EbyKDotOps := sourceOps

abbrev CutState := AspisR1WeightsPairCut.fast_pairing.EbyKDot
abbrev CutWide := AspisR1WeightsPairCut.field.WideExact
abbrev CutQm := AspisR1WeightsPairCut.field.QM31
abbrev SourceState := AspisR1EbyKPushDotBackend.PushState

private theorem bind_ok_value {α β : Type} (x : α) (k : α → Result β) :
    (do let y ← (Result.ok x : Result α); k y) = k x := by
  rfl

/-- The installed constructor returns the explicit zero source state through
its exact typed carrier map. -/
theorem installed_new_zero :
    AspisR1WeightsPairCut.fast_pairing.EbyKDot.new =
      .ok (stateFromSource EbyKNewToPushStateABI.pushZero) := by
  change (do
    let s ← sourceOps.new
    ok (stateFromSource s)) =
      .ok (stateFromSource EbyKNewToPushStateABI.pushZero)
  rw [AspisR1S5EbyKConcreteOpsInstanceV1.sourceOps_new_zero]
  exact bind_ok_value _ (fun s => Result.ok (stateFromSource s))

/-- Starting from the actual installed constructor, the first valid-scalar
push succeeds without any caller-supplied count or accumulator invariant.
It returns the same concrete source-state update and product law as the
source operation theorem. -/
theorem first_push_from_new
    (value : CutWide) (scalar : CutQm)
    (hcanonical : AspisR1EbyKPowerValueCanonicalToPush.pushCanonical
      (wideToSource value))
    (hscalar : ∀ x ∈
      (AspisR1EbyKPushDotBackend.scalarQ (qToSource scalar)).val,
      x.val < 2147483647) :
    ∃ sourceOut : SourceState,
      ∃ initial : CutState,
        AspisR1WeightsPairCut.fast_pairing.EbyKDot.new = .ok initial ∧
        initial = stateFromSource EbyKNewToPushStateABI.pushZero ∧
        AspisR1WeightsPairCut.fast_pairing.EbyKDot.push initial value scalar =
          .ok (.Ok (), stateFromSource sourceOut) ∧
        AspisR1FinishDotCountBoundV2.sumsBelowCount
          sourceOut.count.val sourceOut.c0.sums ∧
        AspisR1FinishDotCountBoundV2.sumsBelowCount
          sourceOut.count.val sourceOut.c1.sums ∧
        sourceOut.count.val = 1 ∧
        AspisR1S5EbyKConcreteOpsWrapperLawsV1.SourcePushUpdate
          EbyKNewToPushStateABI.pushZero sourceOut
          (wideToSource value) (qToSource scalar) := by
  let zero : SourceState := EbyKNewToPushStateABI.pushZero
  let initial : CutState := stateFromSource zero
  have hstate : stateToSource initial = zero := by
    simp [initial, zero, stateToFrom]
  have hcount : (stateToSource initial).count < AspisR1EbyKPushExplicitOpsV1.maxTerms := by
    rw [hstate]
    unfold zero EbyKNewToPushStateABI.pushZero
      AspisR1EbyKPushExplicitOpsV1.maxTerms
    have h : (0#usize : Usize) < (4096#usize : Usize) := by scalar_tac
    simpa only [UScalar.lt_equiv] using h
  have hinv0 : AspisR1FinishDotCountBoundV2.sumsBelowCount
      (stateToSource initial).count.val (stateToSource initial).c0.sums := by
    rw [hstate]
    intro j hj
    have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hcases with h | h | h | h <;> subst j <;>
      simp [zero, EbyKNewToPushStateABI.pushZero,
        AspisR1FinishDotCountBoundV2.sumsBelowCount]
  have hinv1 : AspisR1FinishDotCountBoundV2.sumsBelowCount
      (stateToSource initial).count.val (stateToSource initial).c1.sums := by
    rw [hstate]
    intro j hj
    have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hcases with h | h | h | h <;> subst j <;>
      simp [zero, EbyKNewToPushStateABI.pushZero,
        AspisR1FinishDotCountBoundV2.sumsBelowCount]
  obtain ⟨sourceOut,hpush,hout0,hout1,hinc,hprod⟩ :=
    installed_push_forward_state_step initial value scalar hcanonical
      (by simpa [hstate] using hcount) hscalar
      (by simpa [hstate] using hinv0) (by simpa [hstate] using hinv1)
  have hnew : AspisR1WeightsPairCut.fast_pairing.EbyKDot.new = .ok initial := by
    simpa [initial, zero] using installed_new_zero
  have hinc1 : sourceOut.count.val = 1 := by
    rw [hinc,hstate]
    simp [zero, EbyKNewToPushStateABI.pushZero]
  exact ⟨sourceOut,initial,hnew,rfl,hpush,hout0,hout1,hinc1,hprod⟩

#print axioms installed_new_zero
#print axioms first_push_from_new
end AspisR1S5EbyKPushPairInitializedV1
