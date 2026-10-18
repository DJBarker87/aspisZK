import RRVectorRowBridgeV14
import RRVectorRowNonzeroV5
import RRFiniteCoeffScannerV9

open Polynomial
noncomputable section
namespace RRVectorActualScanner
variable {K : Type*} [Field K] [DecidableEq K]
open RRVectorRowPolynomialBridge

def rowsUpTo (gs : List (List K)) (a : K) (M L : Nat) : List (List K) :=
  List.ofFn fun i : Fin (L+1) => row gs a M i.val

private theorem firstNonzeroFullRows_at
    (xs : List (List K)) (i : Nat) (hi : i < xs.length)
    (hhit : RRFiniteCoeffScannerV9.rowNonzeroFull (xs[i]'hi) = true)
    (hprev : ∀ j (hj : j < i), RRFiniteCoeffScannerV9.rowNonzeroFull (xs[j]'(by omega)) = false) :
    RRFiniteCoeffScannerV9.firstNonzeroFullRows xs = some (i, xs[i]'hi) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      simpa [RRFiniteCoeffScannerV9.firstNonzeroFullRows] using hhit
    | succ i =>
      have hhead : RRFiniteCoeffScannerV9.rowNonzeroFull x = false := by
        have h := hprev 0 (by omega)
        simpa using h
      have htail : i < xs.length := by simp at hi; omega
      have hhit' : RRFiniteCoeffScannerV9.rowNonzeroFull (xs[i]'htail) = true := by
        simpa using hhit
      have hprev' : ∀ j (hj : j < i), RRFiniteCoeffScannerV9.rowNonzeroFull (xs[j]'(by omega)) = false := by
        intro j hj
        have h := hprev (j+1) (by omega)
        simpa using h
      have hrec := ih i htail hhit' hprev'
      simpa [RRFiniteCoeffScannerV9.firstNonzeroFullRows, hhead] using hrec

theorem actual_row_scanner_finds_first_slice
    (gs : List (List K)) (a : K) (M L : Nat) (p : K[X])
    (hp : p ≠ 0) (hzero : inputPolynomial gs 0 = p)
    (hL : p.rootMultiplicity a ≤ L) :
    ∃ v, v ≤ p.rootMultiplicity a ∧
      RRFiniteCoeffScannerV9.firstNonzeroFullRows (rowsUpTo gs a M L) =
        some (v, row gs a M v) ∧
      (RRActualBivariateTaylorBridge.fixedParentCoeffSlice (inputPolynomial gs) a M v ≠ 0) ∧
      (∀ k < v, RRActualBivariateTaylorBridge.fixedParentCoeffSlice (inputPolynomial gs) a M k = 0) := by
  obtain ⟨v, hv, hne, hzeroPrev, hdeg⟩ :=
    RRActualBivariateTaylorBridge.exists_actual_fixed_parent_first_nonzero_slice
      (inputPolynomial gs) a p M hp hzero
  have hvL : v ≤ L := hv.trans hL
  have hlen : (rowsUpTo gs a M L).length = L+1 := by simp [rowsUpTo]
  have hhit : RRFiniteCoeffScannerV9.rowNonzeroFull (row gs a M v) = true := by
    rw [RRVectorRowScannerBridge.rowNonzero_iff_toPolynomial_ne]
    rw [RRVectorRowPolynomialBridge.rowPolynomial_eq_parentSlice]
    simpa [RRActualBivariateTaylorBridge.fixedParentCoeffSlice] using hne
  have hprev : ∀ k (hk : k < v),
      RRFiniteCoeffScannerV9.rowNonzeroFull (row gs a M k) = false := by
    intro k hk
    have hz := hzeroPrev k hk
    apply Bool.eq_false_of_not_eq_true
    intro ht
    have hpoly := (RRVectorRowScannerBridge.rowNonzero_iff_toPolynomial_ne (row gs a M k)).mp ht
    rw [RRVectorRowPolynomialBridge.rowPolynomial_eq_parentSlice] at hpoly
    exact hpoly (by simpa [RRActualBivariateTaylorBridge.fixedParentCoeffSlice] using hz)
  have hidx : v < (rowsUpTo gs a M L).length := by rw [hlen]; omega
  have hget : (rowsUpTo gs a M L)[v]'hidx = row gs a M v := by
    unfold rowsUpTo
    rw [List.getElem_ofFn]
  have hscan := firstNonzeroFullRows_at (rowsUpTo gs a M L) v hidx (by rw [hget]; exact hhit) (by
    intro k hk
    have hk' : k < v := hk
    have hgetk : (rowsUpTo gs a M L)[k]'(by rw [hlen]; omega) = row gs a M k := by
      unfold rowsUpTo
      rw [List.getElem_ofFn]
    rw [hgetk]
    exact hprev k hk')
  refine ⟨v, hv, ?_, hne, hzeroPrev⟩
  rw [hscan]
  congr 1
  rw [hget]
#print axioms actual_row_scanner_finds_first_slice
end RRVectorActualScanner
