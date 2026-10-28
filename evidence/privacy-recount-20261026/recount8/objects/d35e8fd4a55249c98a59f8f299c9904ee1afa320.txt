import R1Z.PV_RunJoin_PublicFailureOption
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PublicFailureMixture

/-- A common public environment distribution preserves a pointwise privacy
bound. In particular a shared public failure branch of advantage zero adds
no error. This does not assert the native signal has this common law. -/
theorem bound {E : Type} [Fintype E]
    (weight real ideal : E → ℚ) (epsilon : ℚ)
    (nonnegative : ∀ e, 0 ≤ weight e)
    (normalized : ∑ e, weight e = 1)
    (pointwise : ∀ e, |real e - ideal e| ≤ epsilon) :
    |(∑ e, weight e * real e) - (∑ e, weight e * ideal e)| ≤ epsilon := by
  rw [← Finset.sum_sub_distrib]
  simp only [← mul_sub]
  calc
    |∑ e, weight e * (real e - ideal e)| ≤ ∑ e, |weight e * (real e - ideal e)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ e, weight e * |real e - ideal e| := by
      apply Finset.sum_congr rfl
      intro e he
      rw [abs_mul,abs_of_nonneg (nonnegative e)]
    _ ≤ ∑ e, weight e * epsilon := by
      apply Finset.sum_le_sum
      intro e he
      exact mul_le_mul_of_nonneg_left (pointwise e) (nonnegative e)
    _ = epsilon := by rw [← Finset.sum_mul,normalized,one_mul]

#print axioms bound
end R1Z.PV_RunJoin_PublicFailureMixture
