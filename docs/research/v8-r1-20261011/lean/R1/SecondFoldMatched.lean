import R1.RepeatedLift

/-! L2: matched responses for the second fold, transported through the
repeated lift and quartet-average projection proved in L1. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.SecondFoldMatched
open AspisR1.RepeatedLift
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriConcreteEncoderCommutation
open AspisV5FriConcreteEncoderApplicability
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV5FunctionalBatching
open AspisV6PublishedTheoremInterfaces
open AspisV6OneFoldCandidateExtraction
open AspisWide.FinalEncoder AspisWide.Agreement
open AspisWide.DegreeThreeMatched AspisWide.MatchedInstances

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

/-- Repeat each of the four received lanes on the stored child quartets. -/
def liftLanes (g : Fin 4 → SecondWord K) : Fin 4 → FinalWord K :=
  fun i => repeatWord (g i)

/-- Lift the response message and every complete quartet in its support. -/
def liftStrategy (σ : ProximateStrategy K (Fin 65536) (SecondCoefficients K)) :
    ProximateStrategy K (Fin 262144) (FinalCoefficients K) where
  candidate z := liftCoefficients (σ.candidate z)
  support z := (σ.support z).biUnion (fun v => Finset.univ.image (childIndex v))

/-- Symbolic reindexing of a union of quartets; only the four slots are enumerated. -/
private theorem repeatedSupport_eq_map {n : ℕ} (S : Finset (Fin n)) :
    S.biUnion (fun v => Finset.univ.image (childIndex v)) =
      (S.product (Finset.univ : Finset (Fin 4))).map (fibreIndexEquiv n).toEmbedding := by
  ext k
  constructor
  · intro hk
    obtain ⟨v, hv, hk⟩ := Finset.mem_biUnion.mp hk
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_map.mpr ⟨(v, s), Finset.mem_product.mpr ⟨hv, hs⟩, rfl⟩
  · intro hk
    obtain ⟨⟨v, s⟩, hv, rfl⟩ := Finset.mem_map.mp hk
    obtain ⟨hv, hs⟩ := Finset.mem_product.mp hv
    exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image.mpr ⟨s, hs, rfl⟩⟩

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
/-- L2.1: each supported parent contributes exactly four distinct children. -/
theorem liftStrategy_support_card
    (σ : ProximateStrategy K (Fin 65536) (SecondCoefficients K)) (z : K) :
    ((liftStrategy σ).support z).card = 4 * (σ.support z).card := by
  change ((σ.support z).biUnion _).card = _
  rw [repeatedSupport_eq_map]
  simp only [Finset.card_map, Finset.product_eq_sprod, Finset.card_product,
    Finset.card_univ, Fintype.card_fin]
  exact Nat.mul_comm _ _

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
private theorem curveValue_liftLanes (g : Fin 4 → SecondWord K)
    (z : K) (v : Fin 65536) (s : Fin 4) :
    curveValue (liftLanes g) z (childIndex v s) = curveValue g z v := by
  simp only [curveValue, batchedDiscrepancy, liftLanes, repeatWord_child]

/-- L2.2: a support larger than 2389 lifts to one larger than 9557. -/
theorem validResponse_lift (g : Fin 4 → SecondWord K)
    (σ : ProximateStrategy K (Fin 65536) (SecondCoefficients K)) (z : K) :
    ValidResponse secondLinear 2389 g σ z →
      ValidResponse exactFinalEncoder 9557 (liftLanes g) (liftStrategy σ) z := by
  rintro ⟨hcard, hagree⟩
  constructor
  · rw [liftStrategy_support_card]
    omega
  · intro k hk
    obtain ⟨v, hv, hk⟩ := Finset.mem_biUnion.mp hk
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hk
    change curveValue (liftLanes g) z (childIndex v s) =
      exactFinalLinear (liftCoefficients (σ.candidate z)) (childIndex v s)
    rw [curveValue_liftLanes, exactFinalLinear_lift]
    exact hagree v hv

omit [Fintype K] [DecidableEq K] [Algebra (ZMod AspisCircleGroupOrder.P) K] in
private theorem coefficientLane_lift (m : SecondCoefficients K) :
    coefficientLane 64 0 (liftCoefficients m) = m := by
  funext d
  simp only [coefficientLane_apply, liftCoefficients_child, ite_true]

/-- Reading the zero lane encodes the quartet average, even on small supports. -/
private theorem secondLinear_zeroLane (a : FinalCoefficients K) (v : Fin 65536) :
    secondLinear (coefficientLane 64 0 a) v = quartetAverage (exactFinalLinear a) v := by
  simpa only [projectCoefficients_eq_lift, exactFinalLinear_lift] using
    exactFinalLinear_project a v 0

private theorem secondLinear_messageCurve (b : Fin 4 → SecondCoefficients K) (z : K) :
    secondLinear (∑ i : Fin 4, z ^ i.val • b i) =
      fun v => curveValue (fun i => secondLinear (b i)) z v := by
  rw [map_sum]
  simp_rw [map_smul]
  funext v
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    curveValue, batchedDiscrepancy, Fin.sum_univ_four]
  norm_num
  ring

/-- L2.3: project the matching components onto their zero coefficient lanes.
Quartet averaging preserves their supported values. This proves the fixed
statement without a lower bound on the original support. -/
theorem matchingDecomposition_descend (g : Fin 4 → SecondWord K)
    (σ : ProximateStrategy K (Fin 65536) (SecondCoefficients K)) (z : K) :
    HasMatchingDecomposition exactFinalEncoder (liftLanes g) (liftStrategy σ) z →
      HasMatchingDecomposition secondLinear g σ z := by
  intro h
  obtain ⟨components, hsupport, hcandidate⟩ :=
    (final_matchingDecomposition_iff (liftLanes g) (liftStrategy σ) z).mp h
  change liftCoefficients (σ.candidate z) = exactFinalMessageCurve components z at hcandidate
  have hmessage : σ.candidate z =
      ∑ i : Fin 4, z ^ i.val • coefficientLane 64 0 (components i) := by
    have h := congrArg (coefficientLane (K := K) 64 0) hcandidate
    simpa only [coefficientLane_lift, exactFinalMessageCurve, map_sum, map_smul] using h
  refine ⟨fun i => coefficientLane 64 0 (components i), ?_, ?_⟩
  · intro v hv
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro i
    have hchildren (s : Fin 4) :
        exactFinalLinear (components i) (childIndex v s) = g i v := by
      have hk : childIndex v s ∈ (liftStrategy σ).support z :=
        Finset.mem_biUnion.mpr ⟨v, hv,
          Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩⟩
      have hi := (Finset.mem_filter.mp (hsupport hk)).2 i
      change repeatWord (g i) (childIndex v s) =
        exactFinalLinear (components i) (childIndex v s) at hi
      rw [repeatWord_child] at hi
      exact hi.symm
    change g i v = secondLinear (coefficientLane 64 0 (components i)) v
    rw [secondLinear_zeroLane, quartetAverage]
    simp_rw [hchildren]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat]
    have h4 : (4 : K) ≠ 0 := by
      simpa only [show (2 : K) * 2 = 4 by ring] using
        mul_ne_zero (NeZero.ne (2 : K)) (NeZero.ne (2 : K))
    exact (mul_div_cancel_left₀ _ h4).symm
  · change secondLinear (σ.candidate z) = _
    rw [hmessage]
    exact secondLinear_messageCurve _ z

/-- L2.4: lift valid unmatched responses into the existing final-encoder bad set. -/
theorem secondFold_bad_response_challenges_card_le (g : Fin 4 → SecondWord K)
    (σ : ProximateStrategy K (Fin 65536) (SecondCoefficients K)) :
    (goodChallenges secondLinear 2389 g
      (badStrategy secondLinear 2389 g σ)).card ≤ foldChallengeCap := by
  apply (Finset.card_le_card ?_).trans
    (exactFinal_bad_response_challenges_card_le (liftLanes g) (liftStrategy σ))
  intro z hz
  have hbad := (mem_badStrategy_good_iff secondLinear 2389 g σ z).mp hz
  apply (mem_badStrategy_good_iff exactFinalEncoder 9557
    (liftLanes g) (liftStrategy σ) z).mpr
  exact ⟨validResponse_lift g σ z hbad.1,
    fun hmatch => hbad.2 (matchingDecomposition_descend g σ z hmatch)⟩

#print axioms liftStrategy_support_card
#print axioms validResponse_lift
#print axioms matchingDecomposition_descend
#print axioms secondFold_bad_response_challenges_card_le
end AspisR1.SecondFoldMatched
