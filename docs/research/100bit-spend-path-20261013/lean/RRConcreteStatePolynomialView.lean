import RRConcreteState

noncomputable section
namespace AspisR1.RRConcreteStatePolynomialView
open Polynomial CompPoly RRRootDescent RRActualBivariateTaylorBridge
open AspisR1.RRConcreteState RRVectorNormalizedRows RRVectorRowPolynomialBridge
variable {K : Type} [Field K] [BEq K] [LawfulBEq K]

/-- Exact readback of the finite inner-X coefficient representation. -/
theorem parent_inner_slice (g : Nat → K[X]) (M n : Nat) :
    xCoeffSlice (parentFromSlices g M) n = if n ≤ M then g n else 0 := by
  ext j
  rw [xCoeffSlice_coeff, parentFromSlices, Polynomial.finsetSum_coeff,
    Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, liftCoeffPolynomial, Polynomial.coeff_map,
    Polynomial.coeff_mul_C, Polynomial.coeff_X_pow]
  by_cases hn : n ≤ M
  · rw [if_pos hn]
    rw [Finset.sum_eq_single n]
    · simp
    · intro b hb hbn
      simp [Ne.symm hbn]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  · rw [if_neg hn, Polynomial.coeff_zero]
    apply Finset.sum_eq_zero
    intro i hi
    have hni : i ≠ n := by
      have hiM := Finset.mem_range.mp hi
      omega
    simp [Ne.symm hni]

theorem model_specialization (s : RawState K) :
    (model s).map (Polynomial.evalRingHom (0 : K)) = inputPolynomial s.rows 0 := by
  have hread := parent_inner_slice (inputPolynomial s.rows) s.maxX 0
  have hslice : xCoeffSlice (model s) 0 = inputPolynomial s.rows 0 := by
    simpa only [Nat.zero_le, ↓reduceIte, model, actualParent] using hread
  rw [← hslice]
  ext j
  simp only [Polynomial.coeff_map, xCoeffSlice_coeff]
  exact Polynomial.coeff_zero_eq_eval_zero _ |>.symm

theorem model_eval_zero_coeff (s : RawState K) (n : Nat) :
    ((model s).eval 0).coeff n =
      if n < s.maxX+1 then (inputPolynomial s.rows n).coeff 0 else 0 := by
  have hread := congrArg (fun p : K[X] => p.coeff 0)
    (parent_inner_slice (inputPolynomial s.rows) s.maxX n)
  have hsame : ((model s).eval 0).coeff n = (xCoeffSlice (model s) n).coeff 0 := by
    simp only [← Polynomial.coeff_zero_eq_eval_zero, xCoeffSlice_coeff]
  rw [hsame]
  by_cases hn : n ≤ s.maxX
  · simpa only [model, actualParent, hn, ↓reduceIte,
      Nat.lt_succ_iff.mpr hn] using hread
  · have hng : ¬ n < s.maxX+1 := by omega
    simpa only [model, actualParent, hn, ↓reduceIte, hng, Polynomial.coeff_zero] using hread

/-- The executable terminal test is exactly evaluation at the zero tail. -/
theorem zeroColumn_toPoly (s : RawState K) :
    (zeroColumnPolynomial s).toPoly = (model s).eval 0 := by
  ext n
  rw [zeroColumn_coeff, model_eval_zero_coeff]

theorem zeroTest_exact (s : RawState K) :
    zeroTest s = true ↔ (model s).eval 0 = 0 := by
  rw [zeroTest, beq_iff_eq, ← zeroColumn_toPoly]
  exact (CPolynomial.toPoly_eq_zero_iff _).symm

#print axioms parent_inner_slice
#print axioms model_specialization
#print axioms model_eval_zero_coeff
#print axioms zeroColumn_toPoly
#print axioms zeroTest_exact
end AspisR1.RRConcreteStatePolynomialView
