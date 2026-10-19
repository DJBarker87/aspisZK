import ActualRawLongDivisionCost
import CompPoly.Univariate.EuclideanAlgorithm

namespace ActualRawModRemainderCostBridge
open CompPoly

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

def scaledDividend (p q : CPolynomial.Raw F) : CPolynomial.Raw F :=
  CPolynomial.Raw.C q.leadingCoeff⁻¹ • p

def monicScaledDivisor (q : CPolynomial.Raw F) : CPolynomial.Raw F :=
  CPolynomial.Raw.C q.leadingCoeff⁻¹ * q

/-- The actual `%` operation used in the private Euclidean GCD body is field
normalization followed by the retained monic long-division remainder. -/
theorem rawMod_eq_scaledMonicRemainder (p q : CPolynomial.Raw F) :
    p % q = (scaledDividend p q).modByMonic (monicScaledDivisor q) := by
  rfl

/-- The actual raw `%` result is the value projection of the costed mirror of
the exact monic division its implementation invokes. -/
theorem rawMod_eq_costedMonicRemainder (p q : CPolynomial.Raw F) :
    p % q =
      (ActualRawLongDivisionCost.divModByMonicAuxWithCost
        (scaledDividend p q).size (scaledDividend p q) (monicScaledDivisor q)).1.2 := by
  rw [ActualRawLongDivisionCost.divModByMonicWithCost_value]
  rfl

/-- Total coefficient-operation charge for one actual raw `%`: the two scalar
normalization products followed by the existing exact costed monic divider.
The inverse itself is charged as one field operation; machine-word bit costs
for inversion remain outside this model. -/
def rawModWithCost (p q : CPolynomial.Raw F) : CPolynomial.Raw F × Nat :=
  let a := scaledDividend p q
  let b := monicScaledDivisor q
  let div := ActualRawLongDivisionCost.divModByMonicAuxWithCost a.size a b
  (div.1.2,
    1 + ActualRawPowCoefficientBudget.rawMulCoefficientBudget
      (CPolynomial.Raw.C q.leadingCoeff⁻¹) p +
      ActualRawPowCoefficientBudget.rawMulCoefficientBudget
        (CPolynomial.Raw.C q.leadingCoeff⁻¹) q + div.2)

theorem rawModWithCost_value (p q : CPolynomial.Raw F) :
    (rawModWithCost p q).1 = p % q := by
  rw [rawMod_eq_costedMonicRemainder]
  simp [rawModWithCost]

/-- The actual remainder's inner elimination loop is initialized with the
scaled dividend's array length, rather than an unbounded search. -/
theorem rawMod_innerFuel (p q : CPolynomial.Raw F) :
    CPolynomial.Raw.divModByMonicAux (scaledDividend p q) (monicScaledDivisor q) =
      CPolynomial.Raw.divModByMonicAux.go (scaledDividend p q).size
        (scaledDividend p q) (monicScaledDivisor q) := rfl

#print axioms rawMod_eq_scaledMonicRemainder
#print axioms rawMod_eq_costedMonicRemainder
#print axioms rawModWithCost_value
#print axioms rawMod_innerFuel
end ActualRawModRemainderCostBridge
