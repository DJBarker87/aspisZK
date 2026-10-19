import AspisFormal.Pool.AlgorithmicCircleDecoderV7
import AspisFormal.V7ExactOneFoldDomains

/-! Field-generic copy of the mathematical evaluator and distance lemmas in
`Pool/V7C1ConcreteProjectionBinding.lean`. No projection or transcript context
is imported. All coordinates still use the exact stored V7 domains. -/
set_option autoImplicit false
namespace AspisWide.InitialEncoder
open Polynomial
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriInitialCircleEncoderIdentity
open AspisCircleTensorBinding
open AspisV7ExactOneFoldDomains

variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]
  [Fintype K] [DecidableEq K]

/-- The base-field embedding forces odd characteristic. -/
theorem two_ne_zero : (2 : K) ≠ 0 := by
  intro equalZero
  apply AspisCircleGroupOrder.two_ne_zero_ZModP
  apply FaithfulSMul.algebraMap_injective (ZMod AspisCircleGroupOrder.P) K
  simpa only [map_ofNat, map_zero] using equalZero

instance neZeroTwo : NeZero (2 : K) := ⟨two_ne_zero⟩

/-- The exact mathematical V7 initial encoder in the production bit-reversed,
fibre-major order.  This is intentionally an ordinary evaluator, not yet a
claim about the production FFT implementation. -/
noncomputable def exactInitialEncoder :
    InitialMessage K → InitialWord K :=
  fun message index =>
    let point := storedInitialCirclePoint20 index
    let x := algebraMap (ZMod AspisCircleGroupOrder.P) K
      (AspisCircleGroupOrder.X point)
    let y := algebraMap (ZMod AspisCircleGroupOrder.P) K point.1.2
    (initialP0 message).eval x + y * (initialP1 message).eval x

theorem exactInitialP0_degree_lt (message : InitialMessage K) :
    (initialP0 message).natDegree < 512 :=
  initialP0_degree_lt message

theorem exactInitialP1_degree_lt (message : InitialMessage K) :
    (initialP1 message).natDegree < 512 :=
  initialP1_degree_lt message

theorem exactInitialPolynomialPair_injective :
    Function.Injective (fun message : InitialMessage K =>
      (initialP0 message, initialP1 message)) :=
  initialPolynomialPair_injective

/-- The stored order is a permutation of the exact log-20 half-odd coset, so
the generic circle-polynomial root theorem applies without changing its
distance bound. -/
noncomputable def exactInitialEncoderCircleRealization :
    AspisV5FriCircleEncoderDistance.CirclePolynomialRealization
      (exactInitialEncoder (K := K)) where
  point := storedInitialCirclePoint20
  point_injective := storedInitialCirclePoint20_injective
  avoids_west_pole := storedInitialCirclePoint20_x_ne_neg_one
  p0 := initialP0
  p1 := initialP1
  p0_degree_lt := exactInitialP0_degree_lt
  p1_degree_lt := exactInitialP1_degree_lt
  coefficient_pair_injective := exactInitialPolynomialPair_injective
  encoder_eq_circle_eval := by
    intro message index
    rfl

/-- The existing exact circle root-count theorem applied to the concrete
mathematical evaluator. -/
theorem exactInitialEncoder_overlap_cap
    (left right : InitialMessage K) (different : left ≠ right) :
    agreementCount (exactInitialEncoder left)
      (exactInitialEncoder right) ≤ 1024 := by
  have cap := AspisV5FriCircleEncoderDistance.agreementSet_card_le_1024
    exactInitialEncoder exactInitialEncoderCircleRealization
    left right different
  calc
    agreementCount (exactInitialEncoder left) (exactInitialEncoder right) =
        (AspisV5FriCoherentCandidateExtraction.agreementSet
          (exactInitialEncoder left) (exactInitialEncoder right)).card := by
      unfold agreementCount
        AspisV5FriCoherentCandidateExtraction.agreementSet
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro index _
      rfl
    _ ≤ 1024 := cap

#print axioms two_ne_zero
#print axioms exactInitialPolynomialPair_injective
#print axioms exactInitialEncoderCircleRealization
#print axioms exactInitialEncoder_overlap_cap
end AspisWide.InitialEncoder
