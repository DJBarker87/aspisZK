import R1Z.PV_RunJoin_FaultAudit
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_Availability
open scoped BigOperators
open PV_RunJoin_KernelCompletion

/-- A normalized native-outcome kernel can have arbitrary successful-return
availability while every successful raw64 block is conditionally uniform.
The one error tag retains all error mass; it is not uniformly sampled. -/
def kernel {C R : Type} [Fintype R] (availability : C → ℚ) : Kernel C R Unit :=
  ⟨availability,fun c _ => availability c / Fintype.card R,
    fun c _ => 1 - availability c⟩

theorem e1 {C R : Type} [Fintype R] (availability : C → ℚ) :
    E1 (kernel (R := R) availability) := fun _ _ => rfl

theorem normalized {C R : Type} [Fintype R] [Nonempty R]
    (availability : C → ℚ) (c : C) :
    (∑ r, (kernel (R := R) availability).success c r) +
      (∑ e, (kernel (R := R) availability).error c e) = 1 := by
  rw [success_sum _ (e1 availability)]
  simp only [kernel,Finset.sum_const,Finset.card_univ,Fintype.card_unit,
    one_smul]
  ring

theorem nonnegative {C R : Type} [Fintype R]
    (availability : C → ℚ) (bounds : ∀ c, 0 ≤ availability c ∧ availability c ≤ 1)
    (c : C) :
    (∀ r, 0 ≤ (kernel (R := R) availability).success c r) ∧
    (∀ e, 0 ≤ (kernel (R := R) availability).error c e) := by
  constructor
  · intro r
    exact div_nonneg (bounds c).1 (Nat.cast_nonneg _)
  · intro e
    exact sub_nonneg.mpr (bounds c).2

/-- This is a proper normalized/nonnegative countermodel to inferring positive
availability from conditional E1, even on an inhabited successful carrier. -/
theorem total_failure {R : Type} [Fintype R] [Nonempty R] :
    E1 (kernel (R := R) (fun _ : Unit => 0)) ∧
    (∑ r, (kernel (R := R) (fun _ : Unit => 0)).success () r) = 0 ∧
    (∑ e, (kernel (R := R) (fun _ : Unit => 0)).error () e) = 1 := by
  refine ⟨e1 _, ?_, ?_⟩
  · exact success_sum _ (e1 _) ()
  · simp only [kernel,sub_zero,Finset.sum_const,Finset.card_univ,
      Fintype.card_unit,one_smul]

#print axioms e1
#print axioms normalized
#print axioms nonnegative
#print axioms total_failure
end R1Z.PV_RunJoin_Availability
