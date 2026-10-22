import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.Ring.Basic
import Lean.Elab.Tactic.Omega
/-! Symbolic polynomial shape for interpolation basis multiplication.
The bound is arbitrary; no concrete coefficient table is reduced. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitInterpolationPoly48
open Polynomial
open scoped BigOperators
variable {K : Type} [CommRing K]

def poly (n : Nat) (f : Nat → K) : K[X] := ∑ k ∈ Finset.range n, monomial k (f k)

theorem coeff (n k : Nat) (f : Nat → K) :
    (poly n f).coeff k=if k < n then f k else 0 := by
  simp [poly,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial,eq_comm]

theorem mul_coeff (n k : Nat) (f : Nat → K) (j : K) :
    ((X-C j)*poly n f).coeff k=
      (if k=0 then 0 else if k-1 < n then f (k-1) else 0)-
        (if k < n then f k else 0)*j := by
  rw [sub_mul,Polynomial.coeff_sub,Polynomial.coeff_C_mul]
  cases k with
  | zero => simp only [Polynomial.coeff_X_mul_zero,coeff,if_true];ring
  | succ k =>
    simp only [Polynomial.coeff_X_mul,coeff,if_neg (Nat.succ_ne_zero k),Nat.add_sub_cancel]
    ring

/-- The last input coefficient is zero, so multiplication by X-j fits in
n coefficients. The law includes every coefficient above the array bound. -/
theorem mul_shape (n : Nat) (positive : 0 < n) (f g : Nat → K) (j : K)
    (highest : f (n-1)=0)
    (hg : ∀ k, k < n → g k=(if k=0 then 0 else f (k-1))-f k*j) :
    poly n g=(X-C j)*poly n f := by
  ext k
  rw [coeff,mul_coeff]
  by_cases hk : k < n
  · have hp : k-1 < n := by omega
    rw [if_pos hk,if_pos hk,hg k hk,if_pos hp]
  · have hk0 : k≠0 := by omega
    rw [if_neg hk,if_neg hk,if_neg hk0]
    by_cases he : k=n
    · subst k
      rw [if_pos (by omega),highest]
      simp only [zero_mul,sub_zero]
    · rw [if_neg (by omega)]
      simp only [zero_mul,sub_zero]

#print axioms coeff
#print axioms mul_coeff
#print axioms mul_shape
end R1Z.ProverCommitInterpolationPoly48
