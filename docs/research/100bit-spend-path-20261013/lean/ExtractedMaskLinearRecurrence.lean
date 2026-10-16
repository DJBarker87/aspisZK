import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Lean.Elab.Tactic.NormCast

/-! Pure field recurrence for the ten-point suffix/weighted accumulators in
`selected_mask_linears`.  The `maskLinear` definition below is copied from
`R0P.Mask.maskLinear` in `R0P/MaskValue.lean` (source SHA-256
`0f2747b346e2c8880e067b4877f94ee26fd8610c0555384262013a16780edd4a`) to avoid
its broad semantic import closure.  This is a distinct namespace and is not
an imported/proved kernel bridge to `R0P.Mask.maskLinear`.  `ReverseAccumulator.step`
processes k after the state for k+1, matching 9-to-0 order.  No source
refinement is asserted here. -/
set_option autoImplicit false
namespace AspisR1.ExtractedMaskLinearRecurrence

variable {K : Type} [Field K]

/-- Exact body of `R0P.Mask.maskLinear`, retained locally to keep this pure
recurrence module independent of the large semantic theorem imports. -/
def maskLinear (family : Nat) (α : Fin 10 → K) : K :=
  ∑ j : Fin 10, ((3 + 22 * j.val + family * (17 + 8 * j.val) : Nat) : K) * α j

def moment0 (α : Fin 10 → K) : K := ∑ j : Fin 10, α j

def moment1 (α : Fin 10 → K) : K :=
  ∑ j : Fin 10, (j.val : K) * α j

/-- State at the boundary `k`: points `9` down through `k` have been
processed.  `suffix` is their suffix sum.  `weighted` is the accumulated
suffix at each processed nonzero index; index zero is deliberately skipped. -/
inductive ReverseAccumulator (α : Fin 10 → K) : Nat → K → K → Prop where
  | finished : ReverseAccumulator α 10 0 0
  | step {k : Nat} {suffixNext weightedNext : K} (hk : k < 10)
      (tail : ReverseAccumulator α (k + 1) suffixNext weightedNext) :
      ReverseAccumulator α k
        (suffixNext + α ⟨k, hk⟩)
        (if k = 0 then weightedNext
          else weightedNext + (suffixNext + α ⟨k, hk⟩))

private def suffixMomentAt (α : Fin 10 → K) (k : Nat) : K :=
  ∑ j : Fin 10, (if k ≤ j.val then (1 : K) else 0) * α j

private def weightCoefficient (k : Nat) (j : Fin 10) : Nat :=
  if k = 0 then j.val else if k ≤ j.val then j.val - k + 1 else 0

private def weightedMomentAt (α : Fin 10 → K) (k : Nat) : K :=
  ∑ j : Fin 10, (weightCoefficient k j : K) * α j

private theorem suffixMomentAt_step (α : Fin 10 → K) (k : Nat)
    (hk : k < 10) :
    suffixMomentAt α k = suffixMomentAt α (k + 1) + α ⟨k, hk⟩ := by
  classical
  have hpoint (j : Fin 10) :
      (if k ≤ j.val then (1 : K) else 0) * α j =
        ((if k + 1 ≤ j.val then (1 : K) else 0) +
          (if j.val = k then (1 : K) else 0)) * α j := by
    split_ifs <;> simp_all <;> omega
  have hsingle :
      (∑ j : Fin 10, (if j.val = k then (1 : K) else 0) * α j) =
        α ⟨k, hk⟩ := by
    rw [Finset.sum_eq_single ⟨k, hk⟩]
    · simp
    · intro j hj hne
      have hneval : j.val ≠ k := by
        intro heq
        apply hne
        exact Fin.ext heq
      simp [hneval]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
  unfold suffixMomentAt
  calc
    (∑ j : Fin 10, (if k ≤ j.val then (1 : K) else 0) * α j) =
        ∑ j : Fin 10,
          (((if k + 1 ≤ j.val then (1 : K) else 0) +
            (if j.val = k then (1 : K) else 0)) * α j) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hpoint j
    _ = (∑ j : Fin 10, (if k + 1 ≤ j.val then (1 : K) else 0) * α j) +
        (∑ j : Fin 10, (if j.val = k then (1 : K) else 0) * α j) := by
          calc
            _ = ∑ j : Fin 10,
                ((if k + 1 ≤ j.val then (1 : K) else 0) * α j +
                  (if j.val = k then (1 : K) else 0) * α j) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
            _ = _ := Finset.sum_add_distrib
    _ = suffixMomentAt α (k + 1) + α ⟨k, hk⟩ := by
          rw [hsingle]
          rfl

theorem weightCoefficient_step (k : Nat) (j : Fin 10)
    (hk : k < 10) (hk0 : k ≠ 0) :
    weightCoefficient k j =
      weightCoefficient (k + 1) j + (if k ≤ j.val then 1 else 0) := by
  unfold weightCoefficient
  by_cases hkj : k ≤ j.val
  · by_cases hnext : k + 1 ≤ j.val
    · simp [hk0, hkj, hnext]
      omega
    · have heq : j.val = k := by omega
      simp [hk0, hkj, hnext, heq]
  · have hnext : ¬ k + 1 ≤ j.val := by omega
    simp [hk0, hkj, hnext]

private theorem weightedMomentAt_step (α : Fin 10 → K) (k : Nat)
    (hk : k < 10) :
    weightedMomentAt α k =
      if k = 0 then weightedMomentAt α (k + 1)
      else weightedMomentAt α (k + 1) + suffixMomentAt α k := by
  classical
  unfold weightedMomentAt
  by_cases hk0 : k = 0
  · subst k
    simp only [if_pos rfl]
    have hpoint (j : Fin 10) :
        (weightCoefficient 0 j : K) * α j =
          (weightCoefficient 1 j : K) * α j := by
      unfold weightCoefficient
      by_cases hj0 : j.val = 0
      · simp [hj0]
      · have hjpos : 1 ≤ j.val := by omega
        simp [hj0, Nat.sub_add_cancel hjpos]
    calc
      (∑ j : Fin 10, (weightCoefficient 0 j : K) * α j) =
          ∑ j : Fin 10, (weightCoefficient 1 j : K) * α j := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hpoint j
      _ = weightedMomentAt α 1 := rfl
  · simp only [if_neg hk0]
    have hcoeff (j : Fin 10) :
        (weightCoefficient k j : K) =
          (weightCoefficient (k + 1) j : K) +
            (if k ≤ j.val then (1 : K) else 0) := by
      have h := weightCoefficient_step k j hk hk0
      split_ifs at h ⊢ <;>
        exact_mod_cast (congrArg (fun n : Nat => (n : K)) h)
    calc
      (∑ j : Fin 10, (weightCoefficient k j : K) * α j) =
          ∑ j : Fin 10,
            (((weightCoefficient (k + 1) j : K) +
              (if k ≤ j.val then (1 : K) else 0)) * α j) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hcoeff j]
      _ = (∑ j : Fin 10, (weightCoefficient (k + 1) j : K) * α j) +
          (∑ j : Fin 10, (if k ≤ j.val then (1 : K) else 0) * α j) := by
            calc
              _ = ∑ j : Fin 10,
                  ((weightCoefficient (k + 1) j : K) * α j +
                    (if k ≤ j.val then (1 : K) else 0) * α j) := by
                      apply Finset.sum_congr rfl
                      intro j hj
                      ring
              _ = _ := Finset.sum_add_distrib
      _ = weightedMomentAt α (k + 1) + suffixMomentAt α k := rfl

theorem reverseAccumulator_moments (α : Fin 10 → K) {k : Nat}
    {suffix weighted : K} (h : ReverseAccumulator α k suffix weighted) :
    suffix = suffixMomentAt α k ∧ weighted = weightedMomentAt α k := by
  induction h with
  | finished =>
      constructor
      · unfold suffixMomentAt
        symm
        apply Finset.sum_eq_zero
        intro j hj
        have hj10 : ¬ 10 ≤ j.val := by omega
        simp [hj10]
      · unfold weightedMomentAt weightCoefficient
        symm
        apply Finset.sum_eq_zero
        intro j hj
        have hj10 : ¬ 10 ≤ j.val := by omega
        simp [hj10]
  | @step k suffixNext weightedNext hk tail ih =>
      rcases ih with ⟨hs, hw⟩
      constructor
      · rw [hs]
        exact (suffixMomentAt_step α k hk).symm
      · rw [hw, hs, weightedMomentAt_step α k hk]
        by_cases hk0 : k = 0
        · simp [hk0]
        · simp [hk0, suffixMomentAt_step α k hk]

theorem reverseAccumulator_final_moments (α : Fin 10 → K)
    {suffix weighted : K}
    (h : ReverseAccumulator α 0 suffix weighted) :
    suffix = moment0 α ∧ weighted = moment1 α := by
  obtain ⟨hs, hw⟩ := reverseAccumulator_moments α h
  constructor
  · simpa [suffixMomentAt, moment0] using hs
  · simpa [weightedMomentAt, weightCoefficient, moment1] using hw

private theorem linear_sum_identity (α : Fin 10 → K) (a b : K) :
    (∑ j : Fin 10, (a + b * (j.val : K)) * α j) =
      a * moment0 α + b * moment1 α := by
  calc
    (∑ j : Fin 10, (a + b * (j.val : K)) * α j) =
        (∑ j : Fin 10, (a * α j + b * ((j.val : K) * α j))) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = (∑ j : Fin 10, a * α j) +
        (∑ j : Fin 10, b * ((j.val : K) * α j)) := Finset.sum_add_distrib
    _ = a * moment0 α + b * moment1 α := by
          simp only [moment0, moment1, Finset.mul_sum]

theorem maskLinear_zero_eq_moments (α : Fin 10 → K) :
    maskLinear 0 α = (3 : K) * moment0 α + (22 : K) * moment1 α := by
  unfold maskLinear
  have hcoef : ∀ j : Fin 10,
      ((3 + 22 * j.val + 0 * (17 + 8 * j.val) : Nat) : K) =
        (3 : K) + 22 * (j.val : K) := by
    intro j
    push_cast
    ring
  calc
    (∑ j : Fin 10,
        ((3 + 22 * j.val + 0 * (17 + 8 * j.val) : Nat) : K) * α j) =
      ∑ j : Fin 10, ((3 : K) + 22 * (j.val : K)) * α j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hcoef j]
    _ = (3 : K) * moment0 α + (22 : K) * moment1 α :=
      linear_sum_identity α 3 22

theorem maskLinear_sixteen_eq_moments (α : Fin 10 → K) :
    maskLinear 16 α = (275 : K) * moment0 α + (150 : K) * moment1 α := by
  unfold maskLinear
  have hcoef : ∀ j : Fin 10,
      ((3 + 22 * j.val + 16 * (17 + 8 * j.val) : Nat) : K) =
        (275 : K) + 150 * (j.val : K) := by
    intro j
    push_cast
    ring
  calc
    (∑ j : Fin 10,
        ((3 + 22 * j.val + 16 * (17 + 8 * j.val) : Nat) : K) * α j) =
      ∑ j : Fin 10, ((275 : K) + 150 * (j.val : K)) * α j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hcoef j]
    _ = (275 : K) * moment0 α + (150 : K) * moment1 α :=
      linear_sum_identity α 275 150

theorem selected_outputs_of_accumulator_moments
    (α : Fin 10 → K) (suffix weighted : K)
    (hsuffix : suffix = moment0 α) (hweighted : weighted = moment1 α) :
    (3 : K) * suffix + 22 * weighted = maskLinear 0 α ∧
    (275 : K) * suffix + 150 * weighted = maskLinear 16 α := by
  constructor
  · rw [hsuffix, hweighted, maskLinear_zero_eq_moments]
  · rw [hsuffix, hweighted, maskLinear_sixteen_eq_moments]

theorem reverseAccumulator_selected_outputs (α : Fin 10 → K)
    {suffix weighted : K}
    (h : ReverseAccumulator α 0 suffix weighted) :
    (3 : K) * suffix + 22 * weighted = maskLinear 0 α ∧
    (275 : K) * suffix + 150 * weighted = maskLinear 16 α := by
  obtain ⟨hsuffix, hweighted⟩ := reverseAccumulator_final_moments α h
  exact selected_outputs_of_accumulator_moments α suffix weighted
    hsuffix hweighted

#print axioms AspisR1.ExtractedMaskLinearRecurrence.weightCoefficient_step
#print axioms AspisR1.ExtractedMaskLinearRecurrence.reverseAccumulator_moments
#print axioms AspisR1.ExtractedMaskLinearRecurrence.reverseAccumulator_final_moments
#print axioms AspisR1.ExtractedMaskLinearRecurrence.maskLinear_zero_eq_moments
#print axioms AspisR1.ExtractedMaskLinearRecurrence.maskLinear_sixteen_eq_moments
#print axioms AspisR1.ExtractedMaskLinearRecurrence.selected_outputs_of_accumulator_moments
#print axioms AspisR1.ExtractedMaskLinearRecurrence.reverseAccumulator_selected_outputs

end AspisR1.ExtractedMaskLinearRecurrence
