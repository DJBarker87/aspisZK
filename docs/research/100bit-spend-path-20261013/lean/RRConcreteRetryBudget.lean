import RRConcreteTraversalLaw

noncomputable section
namespace AspisR1.RRConcreteRetryBudget
open CompPoly AspisR1.RRConcreteState AspisR1.RRConcreteValidState
open AspisR1.RRConcreteTraversal AspisR1.RRConcreteTraversalLaw
open AspisR1.CompPolyFactorMeanTools
open AspisV8PairedCommitment AspisV8R19.OracleResampling
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

def failureMass (ell q t d : Nat) (s : ValidState ell K) : ℚ :=
  mean (fun H : {i : Nat // i ∈ Finset.range (d * mass ell s)} → Fin t → K × K =>
    abortIndicator (runFromFiniteTape ell q t d s H).1)

theorem mass_le_ell (ell : Nat) (s : ValidState ell K) : mass ell s ≤ ell := by
  calc
    mass ell s = (scalarPolynomial s.val).toPoly.natDegree :=
      CPolynomial.natDegree_toPoly _
    _ = (RRVectorRowPolynomialBridge.inputPolynomial s.val.rows 0).natDegree := by
      rw [scalarPolynomial_toPoly]
    _ ≤ ell := s.property.2 0 (Nat.zero_le _)

theorem failureMass_le (ell q t d : Nat) (s : ValidState ell K)
    (hq : q = Fintype.card K) (hodd : ringChar K ≠ 2) :
    failureMass ell q t d s ≤ (d : ℚ) * (ell : ℚ) * (1/2)^t := by
  calc
    failureMass ell q t d s ≤ (d : ℚ) * (mass ell s : ℚ) * (1/2)^t :=
      run_finite_abort_le ell q t d s hq hodd
    _ ≤ (d : ℚ) * (ell : ℚ) * (1/2)^t := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact_mod_cast mass_le_ell ell s

/-- The sum of the two concrete recovery-failure masses fits well inside the
extractor allowance. The list/caller composition is a separate theorem. -/
theorem two_recovery_failure_sum_lt (q : Nat)
    (s0 s1 : ValidState 112 K)
    (hq : q = Fintype.card K) (hodd : ringChar K ≠ 2) :
    failureMass 112 q 149 1025 s0 + failureMass 112 q 149 256 s1 <
      (1 : ℚ) / 2^131 := by
  have h0 := failureMass_le 112 q 149 1025 s0 hq hodd
  have h1 := failureMass_le 112 q 149 256 s1 hq hodd
  apply lt_of_le_of_lt (add_le_add h0 h1)
  norm_num

theorem two_recovery_failure_sum_le_allowance (q : Nat)
    (s0 s1 : ValidState 112 K)
    (hq : q = Fintype.card K) (hodd : ringChar K ≠ 2) :
    failureMass 112 q 149 1025 s0 + failureMass 112 q 149 256 s1 ≤
      (1 : ℚ) / 2^120 := by
  apply le_trans (le_of_lt (two_recovery_failure_sum_lt q s0 s1 hq hodd))
  norm_num

#print axioms mass_le_ell
#print axioms failureMass_le
#print axioms two_recovery_failure_sum_lt
#print axioms two_recovery_failure_sum_le_allowance
end AspisR1.RRConcreteRetryBudget
