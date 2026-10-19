import RRProgramTraversal

noncomputable section
namespace AspisR1.RRProgramMeanTools
open AspisR1.RRProgramTraversal AspisR1.SequentialProgramInvariants
open AspisR1.CompPolyFactorMeanTools
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
variable {I A X Y : Type} [Fintype A] [Nonempty A]

/-- Monotonicity need only hold on actually reachable answer branches.
Unreachable child-state values need not satisfy the traversal invariant. -/
theorem outMean_all_mono (p : Program I A X) (f g : X → ℚ)
    (h : AllOutcomes p (fun out => f out ≤ g out)) :
    outMean p f ≤ outMean p g := by
  induction p with
  | done x => exact h
  | ask i next ih =>
    change mean (fun a => outMean (next a) f) ≤ mean (fun a => outMean (next a) g)
    exact FS.mean_mono (fun a => ih a (h a))

theorem mapOption_abort_mean (p : Program I A (Option X)) (f : X → Y) :
    outMean (mapOption p f) abortIndicator = outMean p abortIndicator := by
  rw [mapOption, outMean_bind]
  apply outMean_congr
  intro out
  cases out <;> rfl

theorem optionBind_abort_le (p : Program I A (Option X))
    (next : X → Program I A (Option Y)) (B : ℚ) (hB : 0 ≤ B)
    (hnext : ∀ x, outMean (next x) abortIndicator ≤ B) :
    outMean (optionBind p next) abortIndicator ≤ outMean p abortIndicator+B :=
  bind_abort_le p next B hB hnext

/-- A state-dependent continuation budget only has to hold for successful
child lists actually returned by the parent sampler. -/
theorem optionBind_abort_le_on_outcomes (p : Program I A (Option X))
    (next : X → Program I A (Option Y)) (B : ℚ) (hB : 0 ≤ B)
    (hnext : AllOutcomes p (fun out => ∀ x, out = some x →
      outMean (next x) abortIndicator ≤ B)) :
    outMean (optionBind p next) abortIndicator ≤ outMean p abortIndicator+B := by
  rw [optionBind, outMean_bind, ← outMean_add_const]
  apply outMean_all_mono
  apply all_mono _ hnext
  intro out ho
  cases out with
  | none =>
    change (1 : ℚ) ≤ 1+B
    exact le_add_of_nonneg_right hB
  | some x =>
    simpa only [abortIndicator, Option.isSome_some, ↓reduceIte, zero_add] using ho x rfl

#print axioms outMean_all_mono
#print axioms mapOption_abort_mean
#print axioms optionBind_abort_le
#print axioms optionBind_abort_le_on_outcomes
end AspisR1.RRProgramMeanTools
