import R0.PolynomialPair

/-! A fixed coefficient-vector inverse for pairs of degree-bounded initial
circle polynomials. This is algebraic plumbing only. -/

set_option autoImplicit false

namespace AspisR1.NaturalPairInverse

open Polynomial
open AspisR0.PolynomialPair
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriInitialCircleEncoderIdentity
open AspisWide.InitialEncoder
open AspisCircleGroupOrder

noncomputable section
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod P) K]

def naturalCoefficients (n : Nat) (p : K[X]) : Fin n → K :=
  monomialToNatural K n *ᵥ (fun i : Fin n => p.coeff i)

theorem naturalCoefficients_polynomial (n : Nat) (p : K[X]) :
    naturalCoefficientPolynomial (naturalCoefficients (K := K) n p) =
      monomialPolynomial (fun i : Fin n => p.coeff i) := by
  unfold naturalCoefficientPolynomial naturalCoefficients naturalToMonomialCoefficients
  rw [Matrix.mulVec_mulVec, naturalCoeff_mul_monomialToNatural,
    Matrix.one_mulVec]

def pair (p0 p1 : K[X]) : InitialMessage K := fun i =>
  if i.val % 2 = 0 then
    naturalCoefficients (K := K) 512 p0 ⟨i.val / 2, by omega⟩
  else
    naturalCoefficients (K := K) 512 p1 ⟨i.val / 2, by omega⟩

theorem initialP0_pair (p0 p1 : K[X]) :
    initialP0 (pair (K := K) p0 p1) = AspisR0.PolynomialPair.truncate p0 := by
  have heven : evenCoefficients (n := 512) (pair (K := K) p0 p1) =
      naturalCoefficients (K := K) 512 p0 := by
    funext i
    simp [pair, evenCoefficients]
  rw [initialP0, heven, naturalCoefficients_polynomial]
  rfl

theorem initialP1_pair (p0 p1 : K[X]) :
    initialP1 (pair (K := K) p0 p1) = AspisR0.PolynomialPair.truncate p1 := by
  have hodd : oddCoefficients (n := 512) (pair (K := K) p0 p1) =
      naturalCoefficients (K := K) 512 p1 := by
    funext i
    simp [pair, oddCoefficients, Nat.add_div]
  rw [initialP1, hodd, naturalCoefficients_polynomial]
  rfl

theorem pair_bounded (p0 p1 : K[X]) (h0 : p0.natDegree ≤ 511)
    (h1 : p1.natDegree ≤ 511) :
    initialP0 (pair (K := K) p0 p1) = p0 ∧
      initialP1 (pair (K := K) p0 p1) = p1 := by
  exact ⟨(initialP0_pair p0 p1).trans (AspisR0.PolynomialPair.truncate_eq p0 h0),
    (initialP1_pair p0 p1).trans (AspisR0.PolynomialPair.truncate_eq p1 h1)⟩

#print axioms naturalCoefficients_polynomial
#print axioms initialP0_pair
#print axioms initialP1_pair
#print axioms pair_bounded

end
end AspisR1.NaturalPairInverse
