import RawExtractorCostComposedV2
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! A uniform polynomial for the numerical parameter ledger. This does not
assert that the actual extractor meets that ledger or that its parameters
are polynomially bounded by an encoded input size. -/
namespace AspisR1.RawExtractorParameterPolynomial
open RawExtractorCostComposedV2 RawExtractorCostLedger

/-- All varying coordinates are bounded by the same size; overhead constants
are fixed for the entire family, not selected after seeing an input. -/
structure CoordinateBound (p : Parameters) (size a k : Nat) : Prop where
  n : p.n ≤ size
  logSize : p.logSize ≤ size
  listSize : p.listSize ≤ size
  b : p.b ≤ size
  calls : p.calls ≤ size
  depth : p.depth ≤ size
  ell : p.ell ≤ size
  retries : p.retries ≤ size
  constant : p.overheadConstant = a
  degree : p.overheadDegree = k

def diagonal (size a k : Nat) : Parameters where
  n := size
  logSize := size
  listSize := size
  b := size
  calls := size
  depth := size
  ell := size
  retries := size
  overheadConstant := a
  overheadDegree := k

/-- The same polynomial works at every size. Its coefficients and exponent
k depend only on the fixed overhead pair a,k. -/
noncomputable def budgetPolynomial (a k : Nat) : Polynomial Nat :=
  let x : Polynomial Nat := Polynomial.X
  let count := x * (x*x+1) * (x+1) * (x+1)
  let overhead := Polynomial.C a * (x+x+x+x+1)^k
  let gcd := (2*x+1) * (100*x^3+800*x^2+1606*x+5)
  let division := x * (100*(x+4)*(x+4))
  let mul := x*x+(2*x+1)*(100*(2*x+5)*(2*x+5))
  let field := count*gcd+count*division+(count*(2*x))*mul+overhead
  let reads := 7*x*x
  field+reads+(field+reads+overhead)*(x+1)^2

theorem budgetPolynomial_eval (size a k : Nat) :
    (budgetPolynomial a k).eval size = (diagonal size a k).attemptBudget := by
  simp [budgetPolynomial, diagonal, Parameters.attemptBudget,
    Parameters.fieldBudget, Parameters.readBudget, Parameters.overhead,
    Parameters.count, Parameters.mulBudget, gcdBudget, divisionBudget]

theorem attemptBudget_le_diagonal (p : Parameters) (size a k : Nat)
    (h : CoordinateBound p size a k) :
    p.attemptBudget ≤ (diagonal size a k).attemptBudget := by
  rcases h with ⟨hn, hq, hL, hb, hc, hd, he, ht, ha, hk⟩
  unfold Parameters.attemptBudget Parameters.fieldBudget Parameters.readBudget
    Parameters.overhead Parameters.count Parameters.mulBudget gcdBudget divisionBudget
  simp only [diagonal, ha, hk]
  gcongr

/-- Explicit uniform-family consequence. The CoordinateBound hypotheses
must still be proved for an actual parameter-size family. -/
theorem family_polynomial_bound (family : Nat → Parameters)
    (size : Nat → Nat) (a k : Nat)
    (h : ∀ i, CoordinateBound (family i) (size i) a k) :
    ∃ polynomial : Polynomial Nat, ∀ i,
      (family i).attemptBudget ≤ polynomial.eval (size i) := by
  refine ⟨budgetPolynomial a k, ?_⟩
  intro i
  rw [budgetPolynomial_eval]
  exact attemptBudget_le_diagonal (family i) (size i) a k (h i)

#print axioms budgetPolynomial_eval
#print axioms attemptBudget_le_diagonal
#print axioms family_polynomial_bound
end AspisR1.RawExtractorParameterPolynomial
