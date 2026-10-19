import RRConcreteStatePolynomialView

open Polynomial
namespace AspisR1.RRInitialNonzeroRowBridge

open RRVectorRowPolynomialBridge
open AspisR1.RRConcreteState
open AspisR1.RRConcreteStatePolynomialView
open RRActualBivariateTaylorBridge RRVectorNormalizedRows

variable {K : Type} [Field K] [BEq K] [LawfulBEq K]

/-- A nonzero stored parent has a nonzero inner-X coefficient row within
its explicit maxX bound. -/
theorem exists_nonzero_initial_row (s : RawState K) (hQ : model s ≠ 0) :
    ∃ i ≤ s.maxX, inputPolynomial s.rows i ≠ 0 := by
  obtain ⟨j, hjmem⟩ := Polynomial.support_nonempty.mpr hQ
  have hjcoeff : (model s).coeff j ≠ 0 := Polynomial.mem_support_iff.mp hjmem
  obtain ⟨n, hnmem⟩ := Polynomial.support_nonempty.mpr hjcoeff
  have hncoeff : ((model s).coeff j).coeff n ≠ 0 :=
    Polynomial.mem_support_iff.mp hnmem
  have hcoeff : (xCoeffSlice (model s) n).coeff j ≠ 0 := by
    rw [xCoeffSlice_coeff]
    exact hncoeff
  have hread : xCoeffSlice (model s) n =
      if n ≤ s.maxX then inputPolynomial s.rows n else 0 := by
    simpa only [model, actualParent] using
      parent_inner_slice (inputPolynomial s.rows) s.maxX n
  by_cases hbound : n ≤ s.maxX
  · refine ⟨n, hbound, ?_⟩
    intro hz
    apply hcoeff
    rw [hread, if_pos hbound, hz]
    simp
  · have hzero : xCoeffSlice (model s) n = 0 := by
      rw [hread, if_neg hbound]
    exact (hcoeff (by simpa [hzero])).elim

#print axioms exists_nonzero_initial_row
end AspisR1.RRInitialNonzeroRowBridge
