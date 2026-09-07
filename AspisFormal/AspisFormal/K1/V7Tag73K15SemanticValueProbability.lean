import AspisFormal.K1.V7Tag73K15SemanticSamplerFactorization
import AspisFormal.K1.V7Tag73SuccessfulSamplerConditioningCore
import AspisFormal.Pool.V7FixedTupleSemanticSecurity

/-!
# Exact value-space probability for the fixed Tag-73 semantic family

This module works after the 22 complete ordinary samplers have been factored
into nuisance skeletons and exact QM31 values.  It gives exact coordinate
splits for theta, the ten-coordinate zerocheck point, mu, and each adaptive
sumcheck challenge, then proves the elementary per-target probability bounds
used by the fixed-family `30,500 / |QM31|` calculation.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73K15SemanticValueProbability

open MeasureTheory
open AspisK1.V7Tag73K15SemanticSamplerFactorization
open AspisK1.V7Tag73K15SemanticSequentialRouter
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisPool.V7FixedTupleSemanticSecurity
open AspisV5AcceptedSumcheckSourceBridge
open AspisV5AcceptedTerminalResidualExtraction
open AspisV5AdaptiveSumcheckChallengeBound
open AspisV5ComponentCQM31TowerExact
open AspisV5SequentialTerminalChallengeBound
open AspisSumcheckMasking

noncomputable section

abbrev SemanticPointValues := Fin 10 → QM31Exact
abbrev SemanticSumcheckValues := Fin 10 → QM31Exact

def semanticThetaValue (values : SemanticOrdinaryValueFamily) : QM31Exact :=
  values .theta

def semanticPointValue
    (values : SemanticOrdinaryValueFamily) : SemanticPointValues :=
  fun coordinate ↦ values (.zerocheckPoint coordinate)

def semanticMuValue (values : SemanticOrdinaryValueFamily) : QM31Exact :=
  values .mu

def semanticSumcheckValue
    (values : SemanticOrdinaryValueFamily) : SemanticSumcheckValues :=
  fun round ↦ values (.sumcheck round)

abbrev SemanticThetaResidual :=
  SemanticPointValues × QM31Exact × SemanticSumcheckValues

abbrev SemanticPointResidual :=
  QM31Exact × QM31Exact × SemanticSumcheckValues

abbrev SemanticMuResidual :=
  QM31Exact × SemanticPointValues × SemanticSumcheckValues

abbrev OtherSemanticSumcheckValues (round : Fin 10) :=
  {other : Fin 10 // other ≠ round} → QM31Exact

abbrev SemanticSumcheckResidual (round : Fin 10) :=
  QM31Exact × SemanticPointValues × QM31Exact ×
    OtherSemanticSumcheckValues round

/-- Split the complete value schedule at theta. -/
def semanticThetaValueCoordinates :
    SemanticOrdinaryValueFamily ≃ SemanticThetaResidual × QM31Exact where
  toFun values :=
    ((semanticPointValue values, semanticMuValue values,
      semanticSumcheckValue values), semanticThetaValue values)
  invFun pair position :=
    match position with
    | .theta => pair.2
    | .zerocheckPoint coordinate => pair.1.1 coordinate
    | .mu => pair.1.2.1
    | .sumcheck round => pair.1.2.2 round
  left_inv := by intro values; funext position; cases position <;> rfl
  right_inv := by intro pair; rcases pair with ⟨⟨point, mu, sumcheck⟩, theta⟩; rfl

/-- Split the complete value schedule at the ten-coordinate zerocheck point. -/
def semanticPointValueCoordinates :
    SemanticOrdinaryValueFamily ≃ SemanticPointResidual × SemanticPointValues where
  toFun values :=
    ((semanticThetaValue values, semanticMuValue values,
      semanticSumcheckValue values), semanticPointValue values)
  invFun pair position :=
    match position with
    | .theta => pair.1.1
    | .zerocheckPoint coordinate => pair.2 coordinate
    | .mu => pair.1.2.1
    | .sumcheck round => pair.1.2.2 round
  left_inv := by intro values; funext position; cases position <;> rfl
  right_inv := by intro pair; rcases pair with ⟨⟨theta, mu, sumcheck⟩, point⟩; rfl

/-- Split the complete value schedule at mu. -/
def semanticMuValueCoordinates :
    SemanticOrdinaryValueFamily ≃ SemanticMuResidual × QM31Exact where
  toFun values :=
    ((semanticThetaValue values, semanticPointValue values,
      semanticSumcheckValue values), semanticMuValue values)
  invFun pair position :=
    match position with
    | .theta => pair.1.1
    | .zerocheckPoint coordinate => pair.1.2.1 coordinate
    | .mu => pair.2
    | .sumcheck round => pair.1.2.2 round
  left_inv := by intro values; funext position; cases position <;> rfl
  right_inv := by intro pair; rcases pair with ⟨⟨theta, point, sumcheck⟩, mu⟩; rfl

/-- Split one adaptive sumcheck answer from the other nine. -/
def splitSemanticSumcheckAt (round : Fin 10) :
    SemanticSumcheckValues ≃
      OtherSemanticSumcheckValues round × QM31Exact where
  toFun values := (fun other ↦ values other.1, values round)
  invFun pair current :=
    if equal : current = round then pair.2 else pair.1 ⟨current, equal⟩
  left_inv := by
    intro values
    funext current
    by_cases equal : current = round
    · subst current
      simp
    · simp [equal]
  right_inv := by
    intro pair
    apply Prod.ext
    · funext other
      simp [other.2]
    · simp

/-- Split the complete value schedule at one adaptive sumcheck round. -/
def semanticSumcheckValueCoordinates (round : Fin 10) :
    SemanticOrdinaryValueFamily ≃
      SemanticSumcheckResidual round × QM31Exact where
  toFun values :=
    ((semanticThetaValue values, semanticPointValue values,
      semanticMuValue values,
      (splitSemanticSumcheckAt round (semanticSumcheckValue values)).1),
      semanticSumcheckValue values round)
  invFun pair position :=
    match position with
    | .theta => pair.1.1
    | .zerocheckPoint coordinate => pair.1.2.1 coordinate
    | .mu => pair.1.2.2.1
    | .sumcheck current =>
        splitSemanticSumcheckAt round |>.symm
          (pair.1.2.2.2, pair.2) current
  left_inv := by
    intro values
    funext position
    cases position with
    | theta => rfl
    | zerocheckPoint coordinate => rfl
    | mu => rfl
    | sumcheck current =>
        exact congrFun (splitSemanticSumcheckAt round |>.symm_apply_apply
          (semanticSumcheckValue values)) current
  right_inv := by
    rintro ⟨⟨theta, point, mu, other⟩, value⟩
    change
      ((theta, point, mu,
          ((splitSemanticSumcheckAt round)
            ((splitSemanticSumcheckAt round).symm (other, value))).1),
        ((splitSemanticSumcheckAt round)
          ((splitSemanticSumcheckAt round).symm (other, value))).2) =
        ((theta, point, mu, other), value)
    rw [(splitSemanticSumcheckAt round).apply_symm_apply]

/-- Transport a pointwise slice bound through any exact finite coordinate
equivalence. -/
theorem uniform_equiv_dependent_event_probability_le
    {Tape Residual Value : Type}
    [Fintype Tape] [Nonempty Tape]
    [Fintype Residual] [Nonempty Residual]
    [Fintype Value] [Nonempty Value]
    (coordinates : Tape ≃ Residual × Value)
    (event : Set Tape) (target : Set (Residual × Value))
    (covered : event ⊆ coordinates ⁻¹' target)
    (bound : ENNReal)
    (sliceBound : ∀ residual,
      (PMF.uniformOfFintype Value).toOuterMeasure
        (productEventFstSlice target residual) ≤ bound) :
    (PMF.uniformOfFintype Tape).toOuterMeasure event ≤ bound := by
  calc
    (PMF.uniformOfFintype Tape).toOuterMeasure event ≤
        (PMF.uniformOfFintype Tape).toOuterMeasure
          (coordinates ⁻¹' target) :=
      (PMF.uniformOfFintype Tape).toOuterMeasure.mono covered
    _ = (PMF.uniformOfFintype (Residual × Value)).toOuterMeasure target := by
      calc
        _ = ((PMF.uniformOfFintype Tape).map coordinates).toOuterMeasure
              target := by rw [PMF.toOuterMeasure_map_apply]
        _ = _ := by
          rw [AspisV5RankOneOpeningHiding.uniform_map_equiv coordinates]
    _ ≤ bound :=
      uniform_product_event_probability_le_of_every_slice_le target bound
        sliceBound

theorem fixedTerminal_thetaBad_card_le_twenty_four
    (plan : FixedTerminalAlgebraPlan QM31Exact) :
    plan.thetaBad.card ≤ 24 := by
  classical
  by_cases existsNonzero : ∃ row,
      rowConstraintPolynomial plan.basis plan.constraintRows row ≠ 0
  · rw [FixedTerminalAlgebraPlan.thetaBad, dif_pos existsNonzero]
    exact thetaLaneCollision_card_le_twenty_four plan.basis
      plan.constraintRows existsNonzero
  · simp [FixedTerminalAlgebraPlan.thetaBad, existsNonzero]

theorem fixedTerminal_muBad_card_le_one
    (plan : FixedTerminalAlgebraPlan QM31Exact)
    (theta : QM31Exact) (point : SemanticPointValues) :
    (plan.muBad theta point).card ≤ 1 := by
  classical
  by_cases valueNonzero :
      constraintMLE plan.basis plan.constraintRows theta point ≠ 0
  · rw [FixedTerminalAlgebraPlan.muBad, if_pos valueNonzero]
    exact helperCancellationSet_card_le_one
      (constraintMLE plan.basis plan.constraintRows theta point)
      (tableSum plan.helper) valueNonzero
  · simp [FixedTerminalAlgebraPlan.muBad, valueNonzero]

theorem adaptiveDegree27_badAt_card_le
    (plan : AdaptiveDegree27MessagePlan QM31Exact)
    (history : List QM31Exact) :
    (plan.badAt history).card ≤ 27 := by
  classical
  by_cases equal : plan.claimedAt history = plan.referenceAt history
  · simp [AdaptiveDegree27MessagePlan.badAt, equal]
  · rw [AdaptiveDegree27MessagePlan.badAt, if_neg equal]
    exact degree27CollisionSet_card_le _ _ equal

end

end AspisK1.V7Tag73K15SemanticValueProbability
