import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring

/-! Exact field algebra for the pack's cyclic full-output G algorithm.
This does not assert correctness of Rust words, FFT butterflies, fixed tables,
or any privacy/soundness property. Those are separate source obligations.
No challenge-dependent nonzero premise is needed by the intended application:
the hypotheses below concern only its fixed nodes and Fourier roots. -/
set_option autoImplicit false
open Finset
namespace AspisV8R17

theorem cyclic_geometric_value {F : Type*} [Field F]
    (a w : F) (n : Nat) (hw : w ^ n = 1) (ha : 1 - a*w ≠ 0) :
    (∑ j ∈ range n, (a*w)^j) = (1-a^n)/(1-a*w) := by
  apply (eq_div_iff ha).2
  simpa only [mul_pow, hw, mul_one] using geom_sum_mul_neg (a*w) n

theorem cyclic_interchange {F I : Type*} [CommSemiring F] [Fintype I]
    (a c : I → F) (w : F) (n : Nat) :
    (∑ j ∈ range n, (∑ i, c i * a i ^ j) * w ^ j) =
    ∑ i, c i * ∑ j ∈ range n, (a i*w)^j := by
  simp only [sum_mul, mul_sum, mul_pow, mul_assoc]
  exact sum_comm

theorem cyclic_nonsingular_spectrum {F I : Type*} [Field F] [Fintype I]
    (a c : I → F) (w : F) (n : Nat) (hw : w^n = 1)
    (ha : ∀ i, 1-a i*w ≠ 0) :
    (∑ j ∈ range n, (∑ i, c i*a i^j)*w^j) =
    ∑ i, c i * ((1-a i^n)/(1-a i*w)) := by
  rw [cyclic_interchange]
  apply sum_congr rfl
  intro i _
  rw [cyclic_geometric_value (a i) w n hw (ha i)]

theorem cyclic_dc_spectrum {F I : Type*} [Field F] [DecidableEq F] [Fintype I]
    (a c : I → F) (n : Nat) :
    (∑ j ∈ range n, (∑ i, c i*a i^j)) =
    ∑ i, c i * (if a i = 1 then (n : F) else (1-a i^n)/(1-a i)) := by
  classical
  have h := cyclic_interchange a c (1 : F) n
  simp only [one_pow, mul_one] at h
  rw [h]
  apply sum_congr rfl
  intro i _
  by_cases ha : a i = 1
  · simp [ha]
  · rw [if_neg ha]
    congr 1
    exact (eq_div_iff (sub_ne_zero.mpr (Ne.symm ha))).2 (geom_sum_mul_neg (a i) n)

theorem cyclic_numerator_over_denominator
    {F I : Type*} [Field F] [Fintype I] [DecidableEq I]
    (b d : I → F) (hd : ∀ i, d i ≠ 0) :
    (∑ i, b i * ∏ t ∈ univ.erase i, d t) / (∏ t, d t) =
    ∑ i, b i / d i := by
  simp only [div_eq_mul_inv, sum_mul]
  apply sum_congr rfl
  intro i hi
  have hp : (∏ t ∈ univ.erase i, d t) ≠ 0 :=
    prod_ne_zero_iff.mpr (fun t _ => hd t)
  rw [← prod_erase_mul univ d hi]
  rw [mul_inv_rev]
  calc
    (b i * ∏ t ∈ univ.erase i, d t) *
        ((d i)⁻¹ * (∏ t ∈ univ.erase i, d t)⁻¹) =
        (b i * (d i)⁻¹) * ((∏ t ∈ univ.erase i, d t) *
          (∏ t ∈ univ.erase i, d t)⁻¹) := by ring
    _ = b i * (d i)⁻¹ := by rw [mul_inv_cancel₀ hp, mul_one]

theorem cyclic_numerator_spectrum
    {F I : Type*} [Field F] [Fintype I] [DecidableEq I]
    (a c : I → F) (w : F) (n : Nat) (hw : w^n = 1)
    (ha : ∀ i, 1-a i*w ≠ 0) :
    (∑ j ∈ range n, (∑ i, c i*a i^j)*w^j) =
    (∑ i, (c i*(1-a i^n)) * ∏ t ∈ univ.erase i, (1-a t*w)) /
      (∏ t, (1-a t*w)) := by
  rw [cyclic_numerator_over_denominator _ _ ha, cyclic_nonsingular_spectrum a c w n hw ha]
  simp only [mul_div_assoc]

#print axioms cyclic_geometric_value
#print axioms cyclic_interchange
#print axioms cyclic_nonsingular_spectrum
#print axioms cyclic_dc_spectrum
#print axioms cyclic_numerator_over_denominator
#print axioms cyclic_numerator_spectrum
end AspisV8R17
