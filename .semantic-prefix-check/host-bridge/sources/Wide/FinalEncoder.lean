import Wide.InitialEncoder

/-! Field-generic mathematical portion of
`K1/V7Tag73ExactOneFoldEncoderBinding.lean`, excluding transcript and inverse
array packaging. -/
set_option autoImplicit false
namespace AspisWide.FinalEncoder
open AspisCircleGroupOrder AspisCircleTensorBinding
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.InitialEncoder
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriInitialCircleEncoderIdentity
open AspisV6OneFoldCandidateExtraction
open AspisV7ExactOneFoldDomains
noncomputable section
variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]
  [Fintype K] [DecidableEq K]

/-- Exact log-18 natural-line encoder as a QM31-linear map. -/
noncomputable def exactFinalLinear :
    (AspisV6OneFoldCandidateExtraction.FinalCoefficients K) →ₗ[K]
      (AspisV6OneFoldCandidateExtraction.FinalWord K) where
  toFun := fun coefficients index =>
    (naturalCoefficientPolynomial coefficients).eval
      (algebraMap (ZMod AspisCircleGroupOrder.P) K
        (storedFirstLineX18 index))
  map_add' := by
    intro left right
    funext index
    change
      (naturalCoefficientPolynomial (left + right)).eval
          (algebraMap (ZMod AspisCircleGroupOrder.P) K
            (storedFirstLineX18 index)) =
        (naturalCoefficientPolynomial left).eval
            (algebraMap (ZMod AspisCircleGroupOrder.P) K
              (storedFirstLineX18 index)) +
          (naturalCoefficientPolynomial right).eval
            (algebraMap (ZMod AspisCircleGroupOrder.P) K
              (storedFirstLineX18 index))
    rw [naturalCoefficientPolynomial_eval_eq_sum (by norm_num),
      naturalCoefficientPolynomial_eval_eq_sum (by norm_num),
      naturalCoefficientPolynomial_eval_eq_sum (by norm_num)]
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro scalar coefficients
    funext index
    change
      (naturalCoefficientPolynomial (scalar • coefficients)).eval
          (algebraMap (ZMod AspisCircleGroupOrder.P) K
            (storedFirstLineX18 index)) =
        scalar * (naturalCoefficientPolynomial coefficients).eval
          (algebraMap (ZMod AspisCircleGroupOrder.P) K
            (storedFirstLineX18 index))
    rw [naturalCoefficientPolynomial_eval_eq_sum (by norm_num),
      naturalCoefficientPolynomial_eval_eq_sum (by norm_num)]
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

def exactFinalEncoder :
    AspisV6OneFoldCandidateExtraction.FinalCoefficients K →
      AspisV6OneFoldCandidateExtraction.FinalWord K :=
  exactFinalLinear

@[simp] theorem exactFinalLinear_apply
    (coefficients : AspisV6OneFoldCandidateExtraction.FinalCoefficients
      K) (index : Fin 262144) :
    exactFinalLinear coefficients index =
      (naturalCoefficientPolynomial coefficients).eval
        (algebraMap (ZMod AspisCircleGroupOrder.P) K
          (storedFirstLineX18 index)) := rfl

/-- Exact line-evaluation identity used both for distance and decoder
applicability. -/
noncomputable def exactFinalEvaluationIdentity :
    NaturalLineEvaluationIdentity (exactFinalEncoder (K := K)) where
  points := fun index =>
    algebraMap (ZMod AspisCircleGroupOrder.P) K
      (storedFirstLineX18 index)
  points_injective := by
    intro left right equal
    apply storedFirstLineX18_injective
    exact FaithfulSMul.algebraMap_injective (ZMod AspisCircleGroupOrder.P) K equal
  encoder_eq_eval := by
    intro message index
    rfl

theorem exactFinalEncoder_overlap_cap
    (left right : AspisV6OneFoldCandidateExtraction.FinalCoefficients
      K) (different : left ≠ right) :
    (AspisV5FriCoherentCandidateExtraction.agreementSet
      (exactFinalEncoder left) (exactFinalEncoder right)).card ≤
      255 := by
  exact agreementSet_card_le_of_polynomialEvaluation exactFinalEncoder 255
    (naturalLinePolynomialRealization (K := K)
      (n := 256) (m := 262144) (by norm_num)
      exactFinalEncoder exactFinalEvaluationIdentity)
    left right different

theorem exactFinalEncoder_injective : Function.Injective (exactFinalEncoder (K := K)) := by
  intro left right codeEqual
  by_contra different
  have cap := exactFinalEncoder_overlap_cap left right different
  have full : AspisV5FriCoherentCandidateExtraction.agreementSet
      (exactFinalEncoder left) (exactFinalEncoder right) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro index
    simp only [AspisV5FriCoherentCandidateExtraction.agreementSet,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact congrFun codeEqual index
  rw [full] at cap
  norm_num at cap

/-- Embedded slot-zero circle x-coordinate for each stored fibre. -/
def exactCircleX (index : Fin 262144) : K :=
  algebraMap (ZMod AspisCircleGroupOrder.P) K
    (X (storedInitialFibrePoint20 index))

/-- Embedded slot-zero circle y-coordinate for each stored fibre. -/
def exactCircleY (index : Fin 262144) : K :=
  algebraMap (ZMod AspisCircleGroupOrder.P) K
    (storedInitialFibrePoint20 index).1.2

/-- The exact stored circle evaluator is pointwise the radix-four lift of the
exact line encoder. -/
theorem exactInitialEncoder_eq_circleLift :
    exactInitialEncoder (K := K) = fun message =>
      circleLiftEncoder exactFinalLinear exactCircleX exactCircleY message := by
  funext message storedIndex
  suffices childEquality : ∀ (index : Fin 262144) (slot : Fin 4),
      exactInitialEncoder message (childIndex index slot) =
        circleLiftEncoder exactFinalLinear exactCircleX exactCircleY message
          (childIndex index slot) by
    have selected := childEquality (parentIndex (n := 262144) storedIndex)
      (slotIndex (n := 262144) storedIndex)
    rw [childIndex_parentIndex_slotIndex (n := 262144) storedIndex] at selected
    exact selected
  intro index slot
  rw [show circleLiftEncoder exactFinalLinear exactCircleX exactCircleY message
      (childIndex index slot) =
      radix4Evaluate (exactCircleY index) (-exactCircleY index)
        (exactCircleX index)
        (fun lane => exactFinalLinear
          (coefficientLane 256 lane message) index) slot by
      unfold circleLiftEncoder
      simpa only [Pi.neg_apply] using
        (radix4LiftEncoder_apply_child exactFinalLinear exactCircleY
          (-exactCircleY) exactCircleX message index slot)]
  simp only [exactFinalLinear_apply, exactInitialEncoder]
  have lineNode := storedFirstLineX18_eq_doubled_algebraMap
    (K := K) index
  have fibrePoint :
      storedInitialFibrePoint20 index =
        g ^ AspisV6EncoderDistance.initialCircleExponent
          (2 * (AspisV5FriBitReverse.reverseFin 18 index).val) := by
    simpa only [storedInitialFibrePoint20_eq_zpow,
      storedInitialNaturalIndex20_child_zero]
  have negativeNode :
      doubledFactor
          (-(algebraMap (ZMod AspisCircleGroupOrder.P) K
            (X (storedInitialFibrePoint20 index)))) 1 =
        doubledFactor
          (algebraMap (ZMod AspisCircleGroupOrder.P) K
            (X (storedInitialFibrePoint20 index))) 1 := by
    simp only [doubledFactor]
    ring
  rw [storedInitialCirclePoint20_x_slots,
    storedInitialCirclePoint20_y_slots]
  have fourCases (selectedSlot : Fin 4) :
      selectedSlot = 0 ∨ selectedSlot = 1 ∨
        selectedSlot = 2 ∨ selectedSlot = 3 := by
    fin_cases selectedSlot <;> simp
  rcases fourCases slot with hs | hs | hs | hs
  all_goals subst slot
  all_goals
    simp [storedCircleSlotX20, storedCircleSlotY20, exactCircleX,
      exactCircleY, radix4Evaluate, map_neg]
  all_goals
    rw [← fibrePoint]
  all_goals
    rw [initialP0_eval_lanes, initialP1_eval_lanes]
    try rw [negativeNode]
    rw [← lineNode]
  all_goals ring

#print axioms exactFinalLinear
#print axioms exactFinalEncoder_overlap_cap
#print axioms exactFinalEncoder_injective
#print axioms exactInitialEncoder_eq_circleLift
end
end AspisWide.FinalEncoder
