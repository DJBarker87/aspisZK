import RRActualFixedParentConvolutionV7
import RRDenseCoeffVectorV6
open Polynomial
noncomputable section
namespace RRVectorRowBridge
variable {K : Type*} [Field K]
open RRDenseCoeffVector
open RRActualBivariateTaylorBridge

def vectorAt (gs : List (List K)) (i : Nat) : List K := (gs[i]?).getD []
def inputPolynomial (gs : List (List K)) (i : Nat) : K[X] := toPolynomial (vectorAt gs i)
def rowValue (gs : List (List K)) (a : K) (M n j : Nat) : K :=
  if j ≤ n then if n-j ≤ M then taylorCoeffVector (vectorAt gs (n-j)) a j else 0 else 0
def row (gs : List (List K)) (a : K) (M n : Nat) : List K :=
  List.ofFn fun j : Fin (n+1) => rowValue gs a M n j.val

private theorem parent_formula (g : Nat → K[X]) (a : K) (M n j : Nat) :
    (xCoeffSlice (fixedParentSlice g a M) n).coeff j =
      ∑ i ∈ Finset.range (M+1), if n = i+j then (Polynomial.taylor a (g i)).coeff j else 0 := by
  rw [xCoeffSlice_coeff]
  unfold fixedParentSlice
  rw [Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, RRActualBivariateTaylorBridge.coeff_inner_substitution]
  have hprod (i : Nat) (c : K) : (X : K[X])^i * (C c * X^j) = C c * X^(i+j) := by
    calc
      X^i * (C c * X^j) = (X^i * C c) * X^j := by rw [mul_assoc]
      _ = (C c * X^i) * X^j := by rw [mul_comm (X^i) (C c)]
      _ = C c * (X^i * X^j) := by rw [← mul_assoc]
      _ = C c * X^(i+j) := by rw [← pow_add]
  simp_rw [hprod, Polynomial.coeff_C_mul_X_pow]

theorem parentCoefficient_eq_rowValue (gs : List (List K)) (a : K) (M n j : Nat) :
    (xCoeffSlice (fixedParentSlice (inputPolynomial gs) a M) n).coeff j = rowValue gs a M n j := by
  rw [parent_formula]
  classical
  by_cases hjn : j ≤ n
  · let i0 := n-j
    have hi0j : i0+j=n := by simp [i0]; omega
    by_cases hiM : i0 ≤ M
    · have hrange : i0 ∈ Finset.range (M+1) := by simp; omega
      rw [Finset.sum_eq_single i0]
      · have heq : n = i0+j := hi0j.symm
        rw [if_pos heq]
        have ht := taylor_coeff_toPolynomial (vectorAt gs i0) a j
        have hrow : rowValue gs a M n j = taylorCoeffVector (vectorAt gs i0) a j := by
          simp [rowValue, hjn, hiM, i0]
        rw [hrow]
        simpa [inputPolynomial] using ht
      · intro i hi hir
        have hne : n ≠ i+j := by intro heq; apply hir; dsimp [i0]; omega
        simp [hne]
      · intro hnot; exact (hnot hrange).elim
    · have hsum : (∑ i ∈ Finset.range (M+1), if n = i+j then
          (Polynomial.taylor a (inputPolynomial gs i)).coeff j else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hiM' : i ≤ M := by have h := Finset.mem_range.mp hi; omega
        have hne : n ≠ i+j := by
          intro heq
          have : i = i0 := by dsimp [i0]; omega
          subst i
          exact (hiM (by omega)).elim
        simp [hne]
      rw [hsum]
      simp [rowValue, hjn, i0, hiM]
  · have hsum : (∑ i ∈ Finset.range (M+1), if n = i+j then
        (Polynomial.taylor a (inputPolynomial gs i)).coeff j else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hne : n ≠ i+j := by omega
      simp [hne]
    rw [hsum]
    simp [rowValue, hjn]
theorem row_getElem?_eq_parentCoefficient (gs : List (List K)) (a : K) (M n j : Nat)
    (hj : j ≤ n) :
    (row gs a M n)[j]? = some ((xCoeffSlice (fixedParentSlice (inputPolynomial gs) a M) n).coeff j) := by
  change (List.ofFn (fun k : Fin (n+1) => rowValue gs a M n k.val))[j]? = _
  rw [List.getElem?_ofFn]
  have hbound : j < n+1 := by omega
  rw [dif_pos hbound]
  exact congrArg some (parentCoefficient_eq_rowValue gs a M n j).symm

#print axioms parentCoefficient_eq_rowValue
#print axioms row_getElem?_eq_parentCoefficient
end RRVectorRowBridge
