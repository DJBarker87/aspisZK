import R1Z.ProverCommitInterpolationPoly48
/-! Symbolic radix-four polynomial identity; no concrete field reduction. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitRadix50
open Polynomial
open scoped BigOperators
variable {K : Type} [CommRing K]

def block (f : Nat → K) (x : K) (j : Nat) : K :=
  f (4*j)+x*f (4*j+1)+x^2*f (4*j+2)+x^3*f (4*j+3)

def blocks (f : Nat → K) (x : K) : Nat → K
 | 0 => 0
 | n+1 => blocks f x n+block f x n*(x^4)^n

theorem eval_poly (n : Nat) (f : Nat → K) (x : K) :
    (ProverCommitInterpolationPoly48.poly n f).eval x=∑ k ∈ Finset.range n, f k*x^k := by
  simp [ProverCommitInterpolationPoly48.poly,Polynomial.eval_finset_sum,Polynomial.eval_monomial]

theorem block_sum (f : Nat → K) (x : K) (j : Nat) :
    block f x j*(x^4)^j=∑ k ∈ Finset.range 4, f (4*j+k)*x^(4*j+k) := by
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.add_zero,zero_add]
  rw [block]
  simp only [pow_add,pow_mul]
  ring

theorem blocks_poly (f : Nat → K) (x : K) (n : Nat) :
    blocks f x n=(ProverCommitInterpolationPoly48.poly (4*n) f).eval x := by
  induction n with
  | zero => simp [blocks,ProverCommitInterpolationPoly48.poly]
  | succ n ih =>
    rw [blocks,ih,eval_poly,block_sum,eval_poly,Nat.mul_succ,Finset.sum_range_add]

#print axioms eval_poly
#print axioms block_sum
#print axioms blocks_poly
end R1Z.ProverCommitRadix50
