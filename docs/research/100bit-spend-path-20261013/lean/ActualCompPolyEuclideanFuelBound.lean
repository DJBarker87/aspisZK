import CompPoly.Univariate.EuclideanAlgorithm
import ActualCompPolyModPowerStepCount

namespace ActualCompPolyEuclideanFuelBound
open CompPoly

/-- The exact fuel supplied by the retained executable GCD wrapper. -/
def gcdMonicFuel {K : Type} [Field K] [BEq K] [LawfulBEq K]
    (p q : CPolynomial.Raw K) : Nat := Array.size p + Array.size q + 1

/-- The public GCD wrapper is the fuel-bounded Euclidean evaluator with this
explicit initial budget. The evaluator consumes at most one fuel unit per
nonzero-remainder recursive branch. -/
theorem gcdMonic_uses_exact_fuel {K : Type} [Field K] [BEq K] [LawfulBEq K]
    (p q : CPolynomial.Raw K) :
    CPolynomial.Raw.gcdMonic p q = CPolynomial.Raw.gcdMonicWithFuel (gcdMonicFuel p q) p q := by
  rfl

/-- The actual monic long-division auxiliary loop starts with the dividend's
raw array length as its recursion budget. -/
theorem divModByMonicAux_uses_exact_fuel {K : Type} [BEq K] [CommRing K]
    (p q : CPolynomial.Raw K) :
    CPolynomial.Raw.divModByMonicAux p q =
      CPolynomial.Raw.divModByMonicAux.go (Array.size p) p q := by
  rfl

/-- GCD's actual recursion budget is linear in the two input raw lengths. -/
theorem gcdMonic_fuel_le_twice_max {K : Type} [Field K] [BEq K] [LawfulBEq K]
    (p q : CPolynomial.Raw K) :
    gcdMonicFuel p q ≤ 2 * max (Array.size p) (Array.size q) + 1 := by
  simp [gcdMonicFuel, Nat.add_assoc]
  omega

#print axioms gcdMonic_uses_exact_fuel
#print axioms divModByMonicAux_uses_exact_fuel
#print axioms gcdMonic_fuel_le_twice_max
end ActualCompPolyEuclideanFuelBound
