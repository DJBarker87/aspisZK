import V7CallerCurrentReleaseR26AcceptedTailSemantics
import V7CallerCurrentReleaseR26RelationEvaluatorSemantics

/-!
# Exact running-claim arithmetic for the current R26 accepted tail

The control-flow inversion records the generated polynomial evaluator call in
each relation round.  This file applies the current R26 Horner theorem to those
three calls and identifies the value read back from each updated alpha slot
with the transcript challenge written into that slot.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26AcceptedTailArithmetic

open V7CallerCurrentReleaseR26AcceptedTailSnapshot
open V7CallerCurrentReleaseR26AcceptedTailSemantics
open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26RelationEvaluatorSemantics
open AspisV5RelationSumcheckSoundness

abbrev TailState (Trace : Type) :=
  V7CallerCurrentReleaseR26AcceptedTailSnapshot.TailState Trace

private theorem update_one_reads_one
    (values updated : Array field.QM31 4#usize) (value : field.QM31)
    (run : values.update 1#usize value = ok updated) :
    updated.index_usize 1#usize = ok value := by
  simp [Array.update] at run
  subst updated
  simp [Array.index_usize]

private theorem update_two_reads_two
    (values updated : Array field.QM31 4#usize) (value : field.QM31)
    (run : values.update 2#usize value = ok updated) :
    updated.index_usize 2#usize = ok value := by
  simp [Array.update] at run
  subst updated
  simp [Array.index_usize]

private theorem update_three_reads_three
    (values updated : Array field.QM31 4#usize) (value : field.QM31)
    (run : values.update 3#usize value = ok updated) :
    updated.index_usize 3#usize = ok value := by
  simp [Array.update] at run
  subst updated
  simp [Array.index_usize]

/-- The round-one evaluator consumes the challenge just written to alpha slot
one and returns exact evaluation of the decoded degree-six polynomial. -/
theorem RoundOneSourceStep.runningClaimAfter_exact
    {Trace : Type}
    {transcript0 : transcript.Transcript}
    {runningClaim : field.QM31} {weights : sumcheck.WeightAccumulator}
    {alpha : Array field.QM31 4#usize}
    {foldedValues : Array field.QM31 256#usize}
    {relationFields : Array (Array field.QM31 6#usize) 4#usize}
    {after : TailState Trace}
    (source : RoundOneSourceStep transcript0 runningClaim weights alpha
      foldedValues relationFields after)
    (polynomialCanonical : CanonicalArray source.polynomial)
    (alphaCanonical : GeneratedCanonicalQM31 source.alphaOne) :
    GeneratedCanonicalQM31 source.runningClaimAfter ∧
      generatedQm31ToExact source.runningClaimAfter =
        (relationPolynomial (exactCoefficients source.polynomial)).eval
          (generatedQm31ToExact source.alphaOne) := by
  have expectedRead := update_one_reads_one alpha source.alphaAfter
    source.alphaOne source.alphaUpdateSuccess
  have alphaReadExact : source.alphaRead = source.alphaOne := by
    have readSuccess := source.alphaReadSuccess
    rw [expectedRead] at readSuccess
    exact (Result.ok.inj readSuccess).symm
  have alphaReadCanonical : GeneratedCanonicalQM31 source.alphaRead := by
    rw [alphaReadExact]
    exact alphaCanonical
  have evaluated := generated_evaluate_success_relationPolynomial
    source.polynomial source.alphaRead source.runningClaimAfter
    polynomialCanonical alphaReadCanonical source.evaluateSuccess
  rwa [alphaReadExact] at evaluated

/-- The round-two evaluator consumes the challenge just written to alpha slot
two and returns exact evaluation of the decoded degree-six polynomial. -/
theorem RoundTwoSourceStep.runningClaimAfter_exact
    {Trace : Type}
    {transcript0 : transcript.Transcript}
    {runningClaim : field.QM31} {weights : sumcheck.WeightAccumulator}
    {alpha : Array field.QM31 4#usize}
    {foldedValues : Array field.QM31 256#usize}
    {relationFields : Array (Array field.QM31 6#usize) 4#usize}
    {after : TailState Trace}
    (source : RoundTwoSourceStep transcript0 runningClaim weights alpha
      foldedValues relationFields after)
    (polynomialCanonical : CanonicalArray source.polynomial)
    (alphaCanonical : GeneratedCanonicalQM31 source.alphaTwo) :
    GeneratedCanonicalQM31 source.runningClaimAfter ∧
      generatedQm31ToExact source.runningClaimAfter =
        (relationPolynomial (exactCoefficients source.polynomial)).eval
          (generatedQm31ToExact source.alphaTwo) := by
  have expectedRead := update_two_reads_two alpha source.alphaAfter
    source.alphaTwo source.alphaUpdateSuccess
  have alphaReadExact : source.alphaRead = source.alphaTwo := by
    have readSuccess := source.alphaReadSuccess
    rw [expectedRead] at readSuccess
    exact (Result.ok.inj readSuccess).symm
  have alphaReadCanonical : GeneratedCanonicalQM31 source.alphaRead := by
    rw [alphaReadExact]
    exact alphaCanonical
  have evaluated := generated_evaluate_success_relationPolynomial
    source.polynomial source.alphaRead source.runningClaimAfter
    polynomialCanonical alphaReadCanonical source.evaluateSuccess
  rwa [alphaReadExact] at evaluated

/-- The round-three evaluator consumes the challenge just written to alpha
slot three and returns exact evaluation of the decoded degree-six polynomial. -/
theorem RoundThreeSourceStep.runningClaimAfter_exact
    {Trace : Type}
    {transcript0 : transcript.Transcript}
    {runningClaim : field.QM31} {weights : sumcheck.WeightAccumulator}
    {alpha : Array field.QM31 4#usize}
    {foldedValues : Array field.QM31 256#usize}
    {relationFields : Array (Array field.QM31 6#usize) 4#usize}
    {after : TailState Trace}
    (source : RoundThreeSourceStep transcript0 runningClaim weights alpha
      foldedValues relationFields after)
    (polynomialCanonical : CanonicalArray source.polynomial)
    (alphaCanonical : GeneratedCanonicalQM31 source.alphaThree) :
    GeneratedCanonicalQM31 source.runningClaimAfter ∧
      generatedQm31ToExact source.runningClaimAfter =
        (relationPolynomial (exactCoefficients source.polynomial)).eval
          (generatedQm31ToExact source.alphaThree) := by
  have expectedRead := update_three_reads_three alpha source.alphaAfter
    source.alphaThree source.alphaUpdateSuccess
  have alphaReadExact : source.alphaRead = source.alphaThree := by
    have readSuccess := source.alphaReadSuccess
    rw [expectedRead] at readSuccess
    exact (Result.ok.inj readSuccess).symm
  have alphaReadCanonical : GeneratedCanonicalQM31 source.alphaRead := by
    rw [alphaReadExact]
    exact alphaCanonical
  have evaluated := generated_evaluate_success_relationPolynomial
    source.polynomial source.alphaRead source.runningClaimAfter
    polynomialCanonical alphaReadCanonical source.evaluateSuccess
  rwa [alphaReadExact] at evaluated

#print axioms RoundOneSourceStep.runningClaimAfter_exact
#print axioms RoundTwoSourceStep.runningClaimAfter_exact
#print axioms RoundThreeSourceStep.runningClaimAfter_exact

end V7CallerCurrentReleaseR26AcceptedTailArithmetic
