import RawExtractorCostComposedBin
import Mathlib.Algebra.Polynomial.Degree.Operations

/-! Fixed protocol coordinates yield an affine numerical ledger, even though
the all-coordinates-varying diagonal polynomial has much larger degree.
This proves the coordinate and polynomial obligations for this family only;
it does not certify any implementation's missing field/bit accounting. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawExtractorFixedProtocolPolynomial
open RawExtractorCostComposedV2 RawExtractorCostLedger
open Polynomial

def family (fixed : Parameters) (Q : Nat) : Parameters :=
  { fixed with logSize := Q + 1161, overheadDegree := 1 }

def slack (p : Parameters) : Nat :=
  p.n + p.listSize + p.b + p.calls + p.depth + p.ell + p.retries + 1161

theorem coordinates (p : Parameters) (Q : Nat) :
    RawExtractorParameterPolynomial.CoordinateBound (family p Q)
      (Q + slack p) p.overheadConstant 1 := by
  constructor
  all_goals dsimp only [family, slack]
  all_goals omega

def arithmeticConstant (p : Parameters) : Nat :=
  p.count * gcdBudget p.n + p.count * divisionBudget p.n +
    (p.count * (2 * p.b)) * p.mulBudget

def budgetPolynomial (p : Parameters) : Polynomial Nat :=
  let q : Polynomial Nat := X + C 1161
  let overhead := C p.overheadConstant * (C p.n + q + C p.listSize + C p.b + 1)
  let field := C (arithmeticConstant p) + overhead
  let reads := C (7 * p.n) * q
  field + reads + (field + reads + overhead) * C ((p.b + 1)^2)

theorem budget_eval (p : Parameters) (Q : Nat) :
    (budgetPolynomial p).eval Q = (family p Q).attemptBudget := by
  simp only [budgetPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one,
    Parameters.attemptBudget, Parameters.fieldBudget, Parameters.readBudget,
    Parameters.overhead, family, Nat.pow_one, arithmeticConstant,
    Parameters.count, Parameters.mulBudget]

/-- Closure at degree one, without expanding protocol constants. -/
theorem degree_add (a b : Polynomial Nat) (ha : a.natDegree ≤ 1)
    (hb : b.natDegree ≤ 1) : (a + b).natDegree ≤ 1 :=
  (Polynomial.natDegree_add_le a b).trans (max_le ha hb)

theorem degree_scale (a : Nat) (p : Polynomial Nat) (hp : p.natDegree ≤ 1) :
    (C a * p).natDegree ≤ 1 := by
  have h := Polynomial.natDegree_mul_le (p := C a) (q := p)
  simp only [Polynomial.natDegree_C, Nat.zero_add] at h
  exact h.trans hp

theorem budget_degree (p : Parameters) : (budgetPolynomial p).natDegree ≤ 1 := by
  have hC (n : Nat) : (C n : Polynomial Nat).natDegree ≤ 1 := by simp
  have hX : (X : Polynomial Nat).natDegree ≤ 1 := by simp
  have hq := degree_add X (C 1161) hX (hC 1161)
  let q : Polynomial Nat := X + C 1161
  let overhead : Polynomial Nat := C p.overheadConstant *
    (C p.n + q + C p.listSize + C p.b + 1)
  have ho : overhead.natDegree ≤ 1 := by
    apply degree_scale
    apply degree_add
    · exact degree_add _ _ (degree_add _ _ (degree_add _ _ (hC p.n) hq)
        (hC p.listSize)) (hC p.b)
    · simpa using hC 1
  have hf := degree_add _ _ (hC (arithmeticConstant p)) ho
  have hr := degree_scale (7 * p.n) q hq
  have hs := degree_add _ _ (degree_add _ _ hf hr) ho
  have ht : ((C (arithmeticConstant p) + overhead + C (7 * p.n) * q + overhead) *
      C ((p.b + 1)^2)).natDegree ≤ 1 := by
    rw [mul_comm]
    exact degree_scale _ _ hs
  exact degree_add _ _ (degree_add _ _ hf hr) ht

#print axioms coordinates
#print axioms budget_eval
#print axioms degree_add
#print axioms degree_scale
#print axioms budget_degree
end AspisR1.RawExtractorFixedProtocolPolynomial
end
