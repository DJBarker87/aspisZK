import ActualRawModRemainderCostBridge
import CompPoly.Univariate.EuclideanAlgorithm

namespace ActualCompPolyGCDCostMirror
open CompPoly ActualRawModRemainderCostBridge

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

/-- Costed mirror of the retained fuel-bounded raw GCD. Each nonterminal
Euclidean step charges its actual `%` implementation via `rawModWithCost`;
that charge includes both scalar-normalization products and all operations in
the exact monic long-division mirror. -/
def gcdMonicWithCost : Nat → CPolynomial.Raw F → CPolynomial.Raw F →
    CPolynomial.Raw F × Nat
  | 0, p, _ => (p.monicNormalize, 0)
  | n + 1, p, q =>
      let p := p.trim
      let q := q.trim
      if (q == 0) = true then (p.monicNormalize, 0)
      else
        let rem := rawModWithCost p q
        let tail := gcdMonicWithCost n q rem.1
        (tail.1, tail.2 + rem.2)
termination_by fuel _ _ => fuel

theorem gcdMonicWithCost_value (fuel : Nat) (p q : CPolynomial.Raw F) :
    (gcdMonicWithCost fuel p q).1 =
      CPolynomial.Raw.gcdMonicWithFuel fuel p q := by
  induction fuel generalizing p q with
  | zero => simp [gcdMonicWithCost, CPolynomial.Raw.gcdMonicWithFuel]
  | succ fuel ih =>
      simp only [gcdMonicWithCost, CPolynomial.Raw.gcdMonicWithFuel]
      split
      · rfl
      · rw [ih, rawModWithCost_value]

/-- Public wrapper uses exactly the same initial GCD fuel, while returning the
sum of actual per-remainder coefficient-operation charges. -/
def gcdMonicWithCostPublic (p q : CPolynomial.Raw F) :
    CPolynomial.Raw F × Nat :=
  gcdMonicWithCost (p.size + q.size + 1) p q

theorem gcdMonicWithCostPublic_value (p q : CPolynomial.Raw F) :
    (gcdMonicWithCostPublic p q).1 = CPolynomial.Raw.gcdMonic p q := by
  simp [gcdMonicWithCostPublic, CPolynomial.Raw.gcdMonic,
    gcdMonicWithCost_value]

#print axioms gcdMonicWithCost_value
#print axioms gcdMonicWithCostPublic_value
end ActualCompPolyGCDCostMirror
