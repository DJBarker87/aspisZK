import Wide.FinalEncoder
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-! Generic copy of `K1/V7Tag73ExactGRSConversion.lean`. The stereographic
parameter is computed in ZMod P before applying the algebra map. -/
set_option autoImplicit false
namespace AspisWide.GRSConversion
open Polynomial
open AspisWide.InitialEncoder AspisWide.FinalEncoder
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5FriCircleEncoderDistance
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriInitialCircleEncoderIdentity
open AspisV7ExactOneFoldDomains
noncomputable section
variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]
  [Fintype K] [DecidableEq K]

private theorem m31_neg_one_not_isSquare :
    ¬ IsSquare (-1 : ZMod AspisCircleGroupOrder.P) := by
  rw [ZMod.exists_sq_eq_neg_one_iff]
  norm_num [AspisCircleGroupOrder.P]

/-! ## Final `256 -> 2^18` line code -/

/-- The exact released final line encoder is a dimension-256 GRS code on the
stored bit-reversed log-18 points, with all column multipliers equal to one. -/
noncomputable def exactFinalGRSConversion :
    ExactGRSConversion 256 255 (exactFinalEncoder (K := K)) where
  messageCoordinates := Equiv.refl _
  points := fun index =>
    algebraMap (ZMod AspisCircleGroupOrder.P) K
      (storedFirstLineX18 index)
  multipliers := fun _ => 1
  messagePolynomial := naturalCoefficientPolynomial
  points_injective := by
    intro left right equal
    apply storedFirstLineX18_injective
    exact FaithfulSMul.algebraMap_injective
      (ZMod AspisCircleGroupOrder.P) K equal
  multipliers_ne_zero := fun _ => one_ne_zero
  messagePolynomial_injective := naturalCoefficientPolynomial_injective
  messagePolynomial_degree_le := by
    intro message
    exact naturalCoefficientPolynomial_natDegree_le (by norm_num) message
  coordinate_identity := by
    intro message index
    simp only [exactFinalEncoder, exactFinalLinear_apply,
      generalizedReedSolomonEncode, one_mul]

theorem exactFinalEncoder_eq_grs (message : FinalMessage K) :
    exactFinalEncoder message = exactFinalGRSConversion.grsEncoder message :=
  exactFinalGRSConversion.releasedEncoder_eq_grsEncoder message

theorem exactFinalAgreementCount_eq_grs
    (received : FinalWord K) (message : FinalMessage K) :
    agreementCount received (exactFinalEncoder message) =
      agreementCount received (exactFinalGRSConversion.grsEncoder message) :=
  exactFinalGRSConversion.agreementCount_eq received message

theorem exactFinalThreshold_transport
    (received : FinalWord K) (message : FinalMessage K) :
    closeAtLeast finalAgreementThreshold exactFinalEncoder received message ↔
      closeAtLeast finalAgreementThreshold exactFinalGRSConversion.grsEncoder
        received message :=
  exactFinalGRSConversion.closeAtLeast_iff finalAgreementThreshold received
    message

/-- The final natural-basis map covers every polynomial of degree at most
255, so this instance is the full dimension-256 GRS code, not merely a
subcode. -/
theorem exactFinalMessagePolynomial_complete
    (polynomial : K[X]) (degree : polynomial.natDegree ≤ 255) :
    ∃ message : FinalMessage K,
      (exactFinalGRSConversion (K := K)).messagePolynomial message = polynomial := by
  simp only [exactFinalGRSConversion]
  exact naturalCoefficientPolynomial_complete (n := 256) (by norm_num)
    polynomial (by simpa using degree)

theorem exactFinal9558_transport
    (received : FinalWord K) (message : FinalMessage K) :
    closeAtLeast 9558 exactFinalEncoder received message ↔
      closeAtLeast 9558 exactFinalGRSConversion.grsEncoder received message := by
  simpa only [finalAgreementThreshold] using
    exactFinalThreshold_transport received message

/-! ## Initial `1024 -> 2^20` circle code -/

/-- The release-specific stereographic numerator from the existing exact
circle realization.  It clears 512 powers of `1+t²`, has degree at most
1024, and is injective on the released 1024-dimensional message subspace. -/
noncomputable def exactCircleGRSPolynomial
    (message : InitialMessage K) : K[X] :=
  circleNumerator
    ((exactInitialEncoderCircleRealization (K := K)).p0 message)
    ((exactInitialEncoderCircleRealization (K := K)).p1 message)

/-- Exact stereographic evaluation point in the deployed stored log-20
coordinate order. -/
def exactCircleGRSPoint (index : Fin 1048576) : K :=
  algebraMap (ZMod AspisCircleGroupOrder.P) K
    (((exactInitialEncoderCircleRealization (K := K)).point index).1.2 /
      (1 + AspisCircleGroupOrder.X
        ((exactInitialEncoderCircleRealization (K := K)).point index)))

@[simp] theorem exactCircleGRSPolynomial_eq_released
    (message : InitialMessage K) :
    exactCircleGRSPolynomial message =
      circleNumerator (initialP0 message) (initialP1 message) := by
  simp only [exactCircleGRSPolynomial, exactInitialEncoderCircleRealization]

@[simp] theorem exactCircleGRSPoint_eq_stored (index : Fin 1048576) :
    exactCircleGRSPoint index =
      algebraMap (ZMod AspisCircleGroupOrder.P) K
        ((storedInitialCirclePoint20 index).1.2 /
          (1 + AspisCircleGroupOrder.X
            (storedInitialCirclePoint20 index))) := rfl

/-- Nonzero GRS column multiplier obtained by undoing the 512 cleared
stereographic denominator powers. -/
def exactCircleGRSMultiplier (index : Fin 1048576) : K :=
  ((1 + exactCircleGRSPoint index ^ 2) ^ 512)⁻¹

theorem exactCircleGRSPoint_injective :
    Function.Injective (exactCircleGRSPoint (K := K)) :=
  exactInitialEncoderCircleRealization.parameter_injective

private theorem exactCircleDenominator_ne_zero (index : Fin 1048576) :
    1 + exactCircleGRSPoint (K := K) index ^ 2 ≠ 0 := by
  let parameter : (ZMod AspisCircleGroupOrder.P) :=
    ((exactInitialEncoderCircleRealization (K := K)).point index).1.2 /
      (1 + AspisCircleGroupOrder.X
        ((exactInitialEncoderCircleRealization (K := K)).point index))
  have pointEq : exactCircleGRSPoint index =
      algebraMap (ZMod AspisCircleGroupOrder.P) K parameter := by
    rfl
  rw [pointEq]
  intro zero
  apply m31_neg_one_not_isSquare
  refine ⟨parameter, ?_⟩
  have mapped : algebraMap (ZMod AspisCircleGroupOrder.P) K (1 + parameter ^ 2) = 0 := by
    simpa only [map_add, map_one, map_pow, map_zero] using zero
  have base : 1 + parameter ^ 2 = 0 :=
    FaithfulSMul.algebraMap_injective (ZMod AspisCircleGroupOrder.P) K
      (mapped.trans (map_zero _).symm)
  have square : parameter ^ 2 = -1 := by
    linear_combination base
  simpa only [pow_two] using square.symm

theorem exactCircleGRSMultiplier_ne_zero (index : Fin 1048576) :
    exactCircleGRSMultiplier (K := K) index ≠ 0 := by
  unfold exactCircleGRSMultiplier
  exact inv_ne_zero (pow_ne_zero 512 (exactCircleDenominator_ne_zero index))

theorem exactCircleGRSPolynomial_degree_le
    (message : InitialMessage K) :
    (exactCircleGRSPolynomial message).natDegree ≤ 1024 := by
  exact circleNumerator_natDegree_le _ _

theorem exactCircleGRSPolynomial_injective :
    Function.Injective (exactCircleGRSPolynomial (K := K)) :=
  exactInitialEncoderCircleRealization.numerator_injective

theorem exactInitialEncoder_coordinate_grs
    (message : InitialMessage K) (index : Fin 1048576) :
    exactInitialEncoder message index =
      generalizedReedSolomonEncode exactCircleGRSPoint
        exactCircleGRSMultiplier (exactCircleGRSPolynomial message) index := by
  unfold generalizedReedSolomonEncode exactCircleGRSMultiplier
  unfold exactCircleGRSPolynomial exactCircleGRSPoint
  have denominatorPowerNonzero :
      (1 +
          (algebraMap (ZMod AspisCircleGroupOrder.P) K)
            (((exactInitialEncoderCircleRealization (K := K)).point index).1.2 /
              (1 + AspisCircleGroupOrder.X
                ((exactInitialEncoderCircleRealization (K := K)).point index))) ^ 2) ^
        512 ≠ 0 := by
    simpa only [exactCircleGRSPoint] using
      pow_ne_zero 512 (exactCircleDenominator_ne_zero index)
  rw [exactInitialEncoderCircleRealization.encoder_numerator_eval]
  rw [← mul_assoc, inv_mul_cancel₀ denominatorPowerNonzero, one_mul]

/-- The exact released initial circle encoder is a 1024-dimensional subcode
of the degree-at-most-1024 ambient GRS code after the explicit stereographic
message transform and nonzero coordinate multipliers above.  Its GRS
coordinates remain in the released bit-reversed order, so the coordinate
permutation is the identity. -/
noncomputable def exactInitialGRSConversion :
    ExactGRSConversion 1024 1024 (exactInitialEncoder (K := K)) where
  messageCoordinates := Equiv.refl _
  points := exactCircleGRSPoint
  multipliers := exactCircleGRSMultiplier
  messagePolynomial := exactCircleGRSPolynomial
  points_injective := exactCircleGRSPoint_injective
  multipliers_ne_zero := exactCircleGRSMultiplier_ne_zero
  messagePolynomial_injective := exactCircleGRSPolynomial_injective
  messagePolynomial_degree_le := exactCircleGRSPolynomial_degree_le
  coordinate_identity := exactInitialEncoder_coordinate_grs

theorem exactInitialEncoder_eq_grs (message : InitialMessage K) :
    exactInitialEncoder message =
      exactInitialGRSConversion.grsEncoder message :=
  exactInitialGRSConversion.releasedEncoder_eq_grsEncoder message

theorem exactInitialAgreementCount_eq_grs
    (received : InitialWord K) (message : InitialMessage K) :
    agreementCount received (exactInitialEncoder message) =
      agreementCount received (exactInitialGRSConversion.grsEncoder message) :=
  exactInitialGRSConversion.agreementCount_eq received message

theorem exactInitialThreshold_transport
    (received : InitialWord K) (message : InitialMessage K) :
    closeAtLeast initialAgreementThreshold exactInitialEncoder received message ↔
      closeAtLeast initialAgreementThreshold
        exactInitialGRSConversion.grsEncoder received message :=
  exactInitialGRSConversion.closeAtLeast_iff initialAgreementThreshold received
    message

theorem exactInitial38230_transport
    (received : InitialWord K) (message : InitialMessage K) :
    closeAtLeast 38230 exactInitialEncoder received message ↔
      closeAtLeast 38230 exactInitialGRSConversion.grsEncoder received
        message := by
  simpa only [initialAgreementThreshold] using
    exactInitialThreshold_transport received message

#print axioms exactFinalGRSConversion
#print axioms exactFinalEncoder_eq_grs
#print axioms exactFinalAgreementCount_eq_grs
#print axioms exactFinalThreshold_transport
#print axioms exactFinalMessagePolynomial_complete
#print axioms exactFinal9558_transport
#print axioms exactCircleGRSPoint_injective
#print axioms exactCircleGRSMultiplier_ne_zero
#print axioms exactCircleGRSPolynomial_degree_le
#print axioms exactCircleGRSPolynomial_injective
#print axioms exactInitialEncoder_coordinate_grs
#print axioms exactInitialGRSConversion
#print axioms exactInitialEncoder_eq_grs
#print axioms exactInitialAgreementCount_eq_grs
#print axioms exactInitialThreshold_transport
#print axioms exactInitial38230_transport

end

end AspisWide.GRSConversion
