import AspisV8R19.CausalFirstHitUnionBound
import FS.LemmaA
import Mathlib.Data.Fintype.Option

set_option autoImplicit false
namespace AspisR1.FiniteOptionSamplerComposition
noncomputable section
attribute [local instance] Classical.propDecidable
open AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound

variable {X Y : Type} [Fintype X] [Nonempty X] [Fintype Y]

/-- Rejection counts as failure; otherwise test the sampled output. -/
def fails (sample : X → Option Y) (bad : Y → Prop) (x : X) : Prop :=
  sample x = none ∨ ∃ y, sample x = some y ∧ bad y

private theorem indicator_fails (sample : X → Option Y) (bad : Y → Prop) (x : X) :
    indicator (fails sample bad x) = indicator (sample x = none) +
      ∑ y : Y, indicator (sample x = some y) * indicator (bad y) := by
  classical
  cases hs : sample x with
  | none => simp [fails, hs, indicator]
  | some y =>
    simp only [fails, hs, Option.some_ne_none, false_or, Option.some.injEq,
      exists_eq_left']
    have hsum : (∑ z : Y, indicator (y = z) * indicator (bad z)) =
        indicator (bad y) := by
      have hpoint : ∀ z : Y, indicator (y = z) * indicator (bad z) =
          if z = y then indicator (bad y) else 0 := by
        intro z
        by_cases h : z = y
        · subst z
          simp [indicator]
        · simp [indicator, h, Ne.symm h]
      simp_rw [hpoint]
      simp
    rw [hsum]
    simp [indicator]

private theorem mean_mul_const (f : X → ℚ) (c : ℚ) :
    mean (fun x => f x * c) = mean f * c := by
  unfold mean
  rw [← Finset.sum_mul]
  ring

/-- A rejecting sampler whose individual output masses are no larger than
uniform adds at most its rejection probability to any downstream bad event.
No independence or cryptographic assumption is introduced by this lemma. -/
theorem failure_le_rejection_add_uniform
    (sample : X → Option Y) (bad : Y → Prop)
    (hmass : ∀ y, mean (fun x => indicator (sample x = some y)) ≤
      1 / (Fintype.card Y : ℚ)) :
    mean (fun x => indicator (fails sample bad x)) ≤
      mean (fun x => indicator (sample x = none)) +
        mean (fun y => indicator (bad y)) := by
  classical
  rw [mean_congr (indicator_fails sample bad), FS.mean_add, mean_sum]
  refine add_le_add le_rfl ?_
  calc
    (∑ y : Y, mean (fun x => indicator (sample x = some y) * indicator (bad y))) =
        ∑ y : Y, mean (fun x => indicator (sample x = some y)) * indicator (bad y) := by
      apply Finset.sum_congr rfl
      intro y hy
      exact mean_mul_const _ _
    _ ≤ ∑ y : Y, (1 / (Fintype.card Y : ℚ)) * indicator (bad y) := by
      apply Finset.sum_le_sum
      intro y hy
      exact mul_le_mul_of_nonneg_right (hmass y) (indicator_nonneg _)
    _ = mean (fun y => indicator (bad y)) := by
      unfold mean
      rw [← Finset.mul_sum]
      ring

/-- Cardinal form of the uniform finite mean, reused from the existing
UniformStateFirstHitMean proof shape without its unrelated collision imports. -/
theorem mean_indicator_count (p : X → Prop) :
    mean (fun x => indicator (p x)) =
      ((Finset.univ.filter p).card : ℚ) / Fintype.card X := by
  classical
  unfold mean indicator
  congr 1
  exact Finset.sum_boole (R := ℚ) p Finset.univ

/-- Exact conditional uniformity and positive success count imply that every
unconditional output mass is bounded by its uniform mass. -/
theorem output_mass_le_uniform_of_conditional
    (sample : X → Option Y)
    (hpos : 0 < (Finset.univ.filter (fun x => (sample x).isSome)).card)
    (huniform : ∀ y,
      (((Finset.univ.filter (fun x => sample x = some y)).card : Nat) : ℚ) /
        ((Finset.univ.filter (fun x => (sample x).isSome)).card : ℚ) =
          1 / (Fintype.card Y : ℚ)) :
    ∀ y, mean (fun x => indicator (sample x = some y)) ≤
      1 / (Fintype.card Y : ℚ) := by
  classical
  intro y
  rw [mean_indicator_count]
  have hsle : (Finset.univ.filter (fun x => (sample x).isSome)).card ≤
      Fintype.card X := by
    exact (Finset.card_filter_le _ _).trans_eq Finset.card_univ
  have hspos : (0 : ℚ) <
      ((Finset.univ.filter (fun x => (sample x).isSome)).card : ℚ) := by
    exact_mod_cast hpos
  calc
    _ ≤ ((Finset.univ.filter (fun x => sample x = some y)).card : ℚ) /
        ((Finset.univ.filter (fun x => (sample x).isSome)).card : ℚ) := by
      have hcount : ((Finset.univ.filter (fun x => (sample x).isSome)).card : ℚ) ≤
          (Fintype.card X : ℚ) := by exact_mod_cast hsle
      convert (div_le_div_of_nonneg_left
        (a := ((Finset.univ.filter (fun x => sample x = some y)).card : ℚ))
        (b := (Fintype.card X : ℚ))
        (c := ((Finset.univ.filter (fun x => (sample x).isSome)).card : ℚ))
        (Nat.cast_nonneg _) hspos hcount) using 1 <;> congr 3
    _ = _ := huniform y

#print axioms failure_le_rejection_add_uniform
#print axioms mean_indicator_count
#print axioms output_mass_le_uniform_of_conditional
end
end AspisR1.FiniteOptionSamplerComposition
