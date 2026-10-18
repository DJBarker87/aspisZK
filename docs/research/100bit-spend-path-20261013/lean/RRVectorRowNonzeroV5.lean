import RRVectorRowBridgeV14
import RRFiniteCoeffScannerV9
open Polynomial
namespace RRVectorRowScannerBridge
variable {K : Type*} [Field K] [DecidableEq K]
open RRDenseCoeffVector

theorem rowNonzero_iff_toPolynomial_ne (xs : List K) :
    RRFiniteCoeffScannerV9.rowNonzeroFull xs = true ↔
      RRDenseCoeffVector.toPolynomial xs ≠ 0 := by
  rw [RRFiniteCoeffScannerV9.rowNonzeroFull_eq_any]
  constructor
  · intro hany
    obtain ⟨x, hxmem, hxne⟩ := List.any_eq_true.mp hany
    have hxne' : x ≠ 0 := by
      have hxdec : decide (x ≠ 0) = true := by simpa using hxne
      exact of_decide_eq_true hxdec
    obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hxmem
    have hcoeff := RRDenseCoeffVector.coeff_toPolynomial xs i
    have hval : RRDenseCoeffVector.coeffAt xs i = x := by
      simp [RRDenseCoeffVector.coeffAt, List.getElem?_eq_getElem hi, hxi]
    intro hp
    have hcne : (RRDenseCoeffVector.toPolynomial xs).coeff i ≠ 0 := by
      intro hc0
      apply hxne'
      have hzero : RRDenseCoeffVector.coeffAt xs i = 0 := by
        rw [← hcoeff]
        simpa [hp] using hc0
      rw [hval] at hzero
      exact hzero
    exact hcne (by rw [hp]; simp)
  · intro hp
    by_contra hnot
    have hfalse : xs.any (fun x => x != 0) = false := Bool.eq_false_of_not_eq_true hnot
    have hall : ∀ x ∈ xs, (x != 0) = false := by
      intro x hx
      exact Bool.eq_false_of_not_eq_true (List.any_eq_false.mp hfalse x hx)
    apply hp
    apply Polynomial.ext
    intro i
    rw [RRDenseCoeffVector.coeff_toPolynomial]
    unfold RRDenseCoeffVector.coeffAt
    by_cases hi : i < xs.length
    · have hget : xs[i]? = some xs[i] := List.getElem?_eq_getElem hi
      rw [hget]
      simp only [Option.getD_some]
      have hmem : xs[i] ∈ xs := List.getElem_mem hi
      have hxzero : (xs[i] != 0) = false := hall _ hmem
      have hdec : decide (xs[i] ≠ 0) = false := by simpa using hxzero
      have hz : xs[i] = 0 := not_ne_iff.mp (of_decide_eq_false hdec)
      simp [hz]
    · have hnone : xs[i]? = none := List.getElem?_eq_none (Nat.not_lt.mp hi)
      simp [hnone]
end RRVectorRowScannerBridge
