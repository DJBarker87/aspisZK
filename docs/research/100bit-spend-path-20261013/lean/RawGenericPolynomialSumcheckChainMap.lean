import RawGenericPolynomialSumcheckChain
import Mathlib.Algebra.Polynomial.Eval.Degree

set_option autoImplicit false
namespace AspisR1PublicPreparation.RawGenericPolynomialSumcheckChainMap

open AspisR1PublicPreparation.RawGenericPolynomialSumcheckChain

/-- A polynomial sumcheck chain is preserved by a ring homomorphism when
both the endpoints, coefficients, and challenges are mapped together. -/
theorem Chain.map {K L : Type} [CommSemiring K] [CommSemiring L]
    (f : K →+* L) {start target : K}
    {entries : List (Polynomial K × K)}
    (h : Chain start target entries) :
    Chain (f start) (f target)
      (entries.map fun e => (e.1.map f, f e.2)) := by
  induction h with
  | nil x =>
      exact .nil (f x)
  | @cons p q rest start mid target hdegree hboundary hnext htail ih =>
      simp only [List.map_cons]
      refine .cons ?_ ?_ ?_ ih
      · exact Nat.le_trans Polynomial.natDegree_map_le hdegree
      · calc
          (p.map f).eval 0 + (p.map f).eval 1
              = f (p.eval 0) + f (p.eval 1) := by
                  rw [← map_zero f, Polynomial.eval_map_apply,
                    ← map_one f, Polynomial.eval_map_apply]
          _ = f (p.eval 0 + p.eval 1) := (map_add f _ _).symm
          _ = f start := congrArg f hboundary
      · calc
          f mid = f (p.eval q) := congrArg f hnext
          _ = (p.map f).eval (f q) := by
                rw [Polynomial.eval_map_apply]

#print axioms Chain.map

end AspisR1PublicPreparation.RawGenericPolynomialSumcheckChainMap
