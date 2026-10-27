import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs

set_option autoImplicit false
namespace AspisR1PublicPreparation.RawGenericPolynomialSumcheckChain

/-- A list of polynomial/challenge pairs whose adjacent values form a
sumcheck chain. This algebraic core has no Rust/extraction dependencies. -/
inductive Chain {K : Type} [CommSemiring K] :
    K → K → List (Polynomial K × K) → Prop
  | nil (x : K) : Chain x x []
  | cons {p : Polynomial K} {q : K} {rest : List (Polynomial K × K)}
      {start mid target : K}
      (degree : p.natDegree ≤ 27)
      (boundary : p.eval 0 + p.eval 1 = start)
      (next : mid = p.eval q)
      (tail : Chain mid target rest) :
      Chain start target ((p, q) :: rest)

end AspisR1PublicPreparation.RawGenericPolynomialSumcheckChain
