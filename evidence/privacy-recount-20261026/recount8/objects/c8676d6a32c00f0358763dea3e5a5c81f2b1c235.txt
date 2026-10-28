import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_KernelCompletion

/-- A conditional successful-return kernel. Error availability is arbitrary;
E1 controls only `success`, normalized by the caller-supplied success mass. -/
structure Kernel (C R E : Type) where
  successMass : C → ℚ
  success : C → R → ℚ
  error : C → E → ℚ

def E1 {C R E : Type} [Fintype R] (k : Kernel C R E) : Prop :=
  ∀ c r, k.success c r = k.successMass c / Fintype.card R

theorem success_sum {C R E : Type} [Fintype R] [Nonempty R]
    (k : Kernel C R E) (e1 : E1 k) (c : C) :
    (∑ r, k.success c r) = k.successMass c := by
  unfold E1 at e1
  simp only [e1,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have nonzero : (Fintype.card R : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem successful_test {C R E : Type} [Fintype R]
    (k : Kernel C R E) (e1 : E1 k) (c : C) (f : R → ℚ) :
    (∑ r, k.success c r * f r) =
      k.successMass c * ((∑ r, f r) / Fintype.card R) := by
  unfold E1 at e1
  simp only [e1]
  rw [← Finset.mul_sum]
  ring

/-- Zero availability is allowed by the exact same E1 statement. This is not
a counterexample to privacy; it prevents inferring availability from E1. -/
theorem zero_success {C R E : Type} [Fintype R] (fault : C → E → ℚ) :
    E1 (Kernel.mk (fun _ => 0) (fun (_ : C) (_ : R) => 0) fault) := by
  intro c r
  simp only [zero_div]

/-- Completion coins for an error are mathematically unused padding. This
formula does NOT replace native partially written bytes by uniform bytes. -/
def errorCompletion {C R E : Type} [Fintype R] (k : Kernel C R E)
    (c : C) (e : E) (_ : R) : ℚ := k.error c e / Fintype.card R

theorem error_completion_sum {C R E : Type} [Fintype R] [Nonempty R]
    (k : Kernel C R E) (c : C) (e : E) :
    (∑ r : R, errorCompletion k c e r) = k.error c e := by
  simp only [errorCompletion,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have nonzero : (Fintype.card R : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

#print axioms success_sum
#print axioms successful_test
#print axioms zero_success
#print axioms error_completion_sum
end R1Z.PV_RunJoin_KernelCompletion
