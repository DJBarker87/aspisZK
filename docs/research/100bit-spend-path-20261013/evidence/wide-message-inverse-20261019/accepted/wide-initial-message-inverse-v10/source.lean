import WideExactInitialCirclePairInverseV5
import AspisFormal.V5FriInitialCircleEncoderIdentity

set_option autoImplicit false
namespace AspisWide.InitialMessageInverse
open Polynomial
open AspisWide.InitialInverse
open AspisWide.InitialCirclePairInverse
open AspisV5FriCircleEncoderDistance
open AspisV5FriInitialCircleEncoderIdentity
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriCoherentCandidateExtraction
open AspisCircleTensorBinding
open Matrix

noncomputable section
variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]
  [Fintype K] [DecidableEq K] [NeZero (2 : K)]

/-- Invert the triangular natural-to-monomial basis change on the first 512
coefficients of a degree-bounded polynomial. -/
def naturalCoefficientsOfPolynomial (p : K[X]) : Fin 512 → K :=
  monomialToNatural K 512 *ᵥ (fun i : Fin 512 => p.coeff i)

theorem naturalCoefficientsOfPolynomial_spec (p : K[X])
    (hp : p.natDegree ≤ 511) :
    naturalCoefficientPolynomial (naturalCoefficientsOfPolynomial p) = p := by
  have hmono : monomialPolynomial (fun i : Fin 512 => p.coeff i) = p := by
    ext d
    by_cases hd : d < 512
    · let i : Fin 512 := ⟨d, hd⟩
      simpa only [i] using
        (monomialPolynomial_coeff (fun i : Fin 512 => p.coeff i) i)
    · have hz := monomialPolynomial_coeff_eq_zero_of_ge
        (fun i : Fin 512 => p.coeff i) d (by omega)
      rw [hz]
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < d)]
  unfold naturalCoefficientPolynomial naturalCoefficientsOfPolynomial
    naturalToMonomialCoefficients
  rw [Matrix.mulVec_mulVec, naturalCoeff_mul_monomialToNatural,
    Matrix.one_mulVec]
  exact hmono

/-- Explicitly interleave the two recovered 512-entry natural-basis vectors. -/
def messageOfPolynomialPair (p0 p1 : K[X]) : Coeff0 K := fun k =>
  if k.val % 2 = 0 then
    naturalCoefficientsOfPolynomial p0 ⟨k.val / 2, by omega⟩
  else
    naturalCoefficientsOfPolynomial p1 ⟨k.val / 2, by omega⟩

theorem messageOfPolynomialPair_spec (p0 p1 : K[X])
    (h0 : p0.natDegree ≤ 511) (h1 : p1.natDegree ≤ 511) :
    initialP0 (messageOfPolynomialPair p0 p1) = p0 ∧
      initialP1 (messageOfPolynomialPair p0 p1) = p1 := by
  have heven : evenCoefficients (n := 512) (messageOfPolynomialPair p0 p1) =
      naturalCoefficientsOfPolynomial p0 := by
    funext i
    simp [evenCoefficients, messageOfPolynomialPair]
  have hodd : oddCoefficients (n := 512) (messageOfPolynomialPair p0 p1) =
      naturalCoefficientsOfPolynomial p1 := by
    funext i
    simp [oddCoefficients, messageOfPolynomialPair, Nat.add_div]
  constructor
  · rw [initialP0, heven, naturalCoefficientsOfPolynomial_spec p0 h0]
  · rw [initialP1, hodd, naturalCoefficientsOfPolynomial_spec p1 h1]

/-- Decode the actual released 1024-entry initial message from its
parity-separated circle numerator. The output is a concrete coefficient
function, not a chosen witness. -/
def decodeCircleInitialMessage
    (nodes0 : Fin 513 → K) (nodes1 : Fin 512 → K)
    (havoid0 : ∀ i, nodes0 i ≠ -1) (havoid1 : ∀ i, nodes1 i ≠ -1)
    (f : K[X]) : Coeff0 K :=
  let p0 := decodeFractionalLift 512 nodes0 havoid0 (evenPart f)
  let p1 := decodeFractionalLift 511 nodes1 havoid1 (oddPart f)
  messageOfPolynomialPair p0 p1

theorem decodeCircleInitialMessage_of_encoded
    (nodes0 : Fin 513 → K) (nodes1 : Fin 512 → K)
    (hinj0 : Function.Injective nodes0) (hinj1 : Function.Injective nodes1)
    (havoid0 : ∀ i, nodes0 i ≠ -1) (havoid1 : ∀ i, nodes1 i ≠ -1)
    (message : Coeff0 K) :
    decodeCircleInitialMessage nodes0 nodes1 havoid0 havoid1
      (circleNumerator (initialP0 message) (initialP1 message)) = message := by
  have hdecoded := decodeCircleNumerator_pair nodes0 nodes1 hinj0 hinj1
    havoid0 havoid1 (initialP0 message) (initialP1 message)
    (by have h := initialP0_degree_lt message; omega)
    (by have h := initialP1_degree_lt message; omega)
  have hpair :
      (decodeFractionalLift 512 nodes0 havoid0
          (evenPart (circleNumerator (initialP0 message) (initialP1 message))),
        decodeFractionalLift 511 nodes1 havoid1
          (oddPart (circleNumerator (initialP0 message) (initialP1 message)))) =
        (initialP0 message, initialP1 message) := hdecoded
  let dp0 := decodeFractionalLift 512 nodes0 havoid0
    (evenPart (circleNumerator (initialP0 message) (initialP1 message)))
  let dp1 := decodeFractionalLift 511 nodes1 havoid1
    (oddPart (circleNumerator (initialP0 message) (initialP1 message)))
  have hpair0 := congrArg Prod.fst hpair
  have hpair1 := congrArg Prod.snd hpair
  have hdp0 : dp0 = initialP0 message := by
    simpa only [Prod.fst, dp0] using hpair0
  have hdp1 : dp1 = initialP1 message := by
    simpa only [Prod.snd, dp1] using hpair1
  have hdeg0 : dp0.natDegree ≤ 511 := by
    rw [hdp0]
    exact Nat.lt_succ_iff.mp (initialP0_degree_lt message)
  have hdeg1 : dp1.natDegree ≤ 511 := by
    rw [hdp1]
    exact Nat.lt_succ_iff.mp (initialP1_degree_lt message)
  have hspec := messageOfPolynomialPair_spec dp0 dp1 hdeg0 hdeg1
  have hpoly0 :
      naturalCoefficientPolynomial (evenCoefficients (n := 512)
        (messageOfPolynomialPair dp0 dp1)) =
      naturalCoefficientPolynomial (evenCoefficients (n := 512) message) := by
    simpa only [initialP0] using hspec.1.trans hdp0
  have hpoly1 :
      naturalCoefficientPolynomial (oddCoefficients (n := 512)
        (messageOfPolynomialPair dp0 dp1)) =
      naturalCoefficientPolynomial (oddCoefficients (n := 512) message) := by
    simpa only [initialP1] using hspec.2.trans hdp1
  have hcoeff0 := naturalCoefficientPolynomial_injective hpoly0
  have hcoeff1 := naturalCoefficientPolynomial_injective hpoly1
  have hvec :
      (evenCoefficients (n := 512) (messageOfPolynomialPair dp0 dp1),
       oddCoefficients (n := 512) (messageOfPolynomialPair dp0 dp1)) =
      (evenCoefficients (n := 512) message, oddCoefficients (n := 512) message) :=
    Prod.ext hcoeff0 hcoeff1
  have hmsg : messageOfPolynomialPair dp0 dp1 = message :=
    evenOddCoefficients_injective hvec
  change messageOfPolynomialPair dp0 dp1 = message
  exact hmsg

#print axioms decodeCircleInitialMessage_of_encoded
end
end AspisWide.InitialMessageInverse
