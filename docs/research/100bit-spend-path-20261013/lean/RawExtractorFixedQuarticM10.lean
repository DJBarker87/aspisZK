import RawExtractorCostComposedBin
import Mathlib.Algebra.Polynomial.Degree.Operations

/-! Fixed protocol coordinates yield an quartic numerical ledger, even though
the all-coordinates-varying diagonal polynomial has much larger degree.
This proves the coordinate and polynomial obligations for this family only;
it does not certify any implementation's missing field/bit accounting. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawExtractorFixedQuarticM10
open RawExtractorCostComposedV2 RawExtractorCostLedger
open Polynomial

def family (fixed : Parameters) (Q : Nat) : Parameters :=
  { fixed with logSize := Q + 1161, overheadDegree := 4 }

def slack (p : Parameters) : Nat :=
  p.n + p.listSize + p.b + p.calls + p.depth + p.ell + p.retries + 1161

theorem coordinates (p : Parameters) (Q : Nat) :
    RawExtractorParameterPolynomial.CoordinateBound (family p Q)
      (Q + slack p) p.overheadConstant 4 := by
  constructor
  all_goals dsimp only [family, slack]
  all_goals omega

def arithmeticConstant (p : Parameters) : Nat :=
  p.count * gcdBudget p.n + p.count * divisionBudget p.n +
    (p.count * (2 * p.b)) * p.mulBudget

def budgetPolynomial (p : Parameters) : Polynomial Nat :=
  let q : Polynomial Nat := X + C 1161
  let overhead := C p.overheadConstant * (C p.n + q + C p.listSize + C p.b + 1)^4
  let field := C (arithmeticConstant p) + overhead
  let reads := C (7 * p.n) * q
  field + reads + (field + reads + overhead) * C ((p.b + 1)^2)

theorem budget_eval (p : Parameters) (Q : Nat) :
    (budgetPolynomial p).eval Q = (family p Q).attemptBudget := by
  simp only [budgetPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_pow,
    Parameters.attemptBudget, Parameters.fieldBudget, Parameters.readBudget,
    Parameters.overhead, family, arithmeticConstant,
    Parameters.count, Parameters.mulBudget]

/-- The fixed family has degree at most four in the query budget. -/
theorem budget_degree (p : Parameters) : (budgetPolynomial p).natDegree ≤ 4 := by
  have hC (n : Nat) : (C n : Polynomial Nat).natDegree ≤ 1 := by simp
  have hX : (X : Polynomial Nat).natDegree ≤ 1 := by simp
  have hadd (a b : Polynomial Nat) (ha : a.natDegree ≤ 1) (hb : b.natDegree ≤ 1) :
      (a+b).natDegree ≤ 1 := (Polynomial.natDegree_add_le _ _).trans (max_le ha hb)
  have hscale (a : Nat) (f : Polynomial Nat) (d : Nat) (h : f.natDegree ≤ d) :
      (C a*f).natDegree ≤ d := by
    have hh := Polynomial.natDegree_mul_le (p := C a) (q := f)
    simp only [Polynomial.natDegree_C,Nat.zero_add] at hh
    exact hh.trans h
  have hq := hadd X (C 1161) hX (hC 1161)
  let q : Polynomial Nat := X+C 1161
  let s : Polynomial Nat := C p.n+q+C p.listSize+C p.b+1
  have hs : s.natDegree ≤ 1 :=
    hadd _ _ (hadd _ _ (hadd _ _ (hadd _ _ (hC p.n) hq) (hC p.listSize)) (hC p.b))
      (by simpa using hC 1)
  have hp : (s^4).natDegree ≤ 4 := by
    exact (Polynomial.natDegree_pow_le).trans (by omega)
  let o : Polynomial Nat := C p.overheadConstant*s^4
  have ho : o.natDegree ≤ 4 := hscale _ _ _ hp
  have add3 (a b : Polynomial Nat) (ha : a.natDegree ≤ 4) (hb : b.natDegree ≤ 4) :
      (a+b).natDegree ≤ 4 := (Polynomial.natDegree_add_le _ _).trans (max_le ha hb)
  have hf := add3 _ _ ((hC (arithmeticConstant p)).trans (by omega)) ho
  have hr : (C (7*p.n)*q).natDegree ≤ 4 := (hscale _ _ _ hq).trans (by omega)
  have hh := add3 _ _ (add3 _ _ hf hr) ho
  have ht : ((C (arithmeticConstant p)+o+C (7*p.n)*q+o)*C ((p.b+1)^2)).natDegree ≤ 4 := by
    rw [mul_comm]
    exact hscale _ _ _ hh
  exact add3 _ _ (add3 _ _ hf hr) ht

#print axioms coordinates
#print axioms budget_eval
#print axioms budget_degree
end AspisR1.RawExtractorFixedQuarticM10
end
