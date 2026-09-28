import V7CallerCurrentReleaseR26RelationEvaluatorSemantics
import V7CallerCurrentReleaseR26K1QueryWeightBridge
import AspisFormal.V6TranscriptRelationGrammar

/-!
# Exact current R26 compact relation-polynomial decoding

The source receives coefficients `0,1,2,3,5,6` and reconstructs coefficient
four as `incoming / 4 - c0`.  This file proves that the literal R26 decoder
produces exactly the maintained `relationCoefficient` vector.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26RelationDecodeSemantics

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26RelationEvaluatorSemantics
open V7CallerCurrentReleaseR26K1QueryWeightBridge
open AspisV6TranscriptRelationGrammar

abbrev RawQM31 := field.QM31
abbrev SourceQM31 := V7CallerCurrentReleaseR26FieldBridge.ExactQM31
abbrev ModelQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

def CanonicalRelationRow (sent : Array RawQM31 6#usize) : Prop :=
  ∀ index, index < 6 → GeneratedCanonicalQM31 sent.val[index]!

def exactRelationParts (sent : Array RawQM31 6#usize) :
    RelationRoundParts ModelQM31 where
  c0 := sourceQm31ToModel (generatedQm31ToExact sent.val[0]!)
  c1 := sourceQm31ToModel (generatedQm31ToExact sent.val[1]!)
  c2 := sourceQm31ToModel (generatedQm31ToExact sent.val[2]!)
  c3 := sourceQm31ToModel (generatedQm31ToExact sent.val[3]!)
  c5 := sourceQm31ToModel (generatedQm31ToExact sent.val[4]!)
  c6 := sourceQm31ToModel (generatedQm31ToExact sent.val[5]!)

/-- Exact source-field image of the deployed base-field quarter constant. -/
def sourceQuarter : ModelQM31 := sourceQm31ToModel
  (generatedM31ScalarToExactQM31 field.M31_QUARTER)

theorem sourceQuarter_mul_four : sourceQuarter * 4 = 1 := by
  unfold sourceQuarter generatedM31ScalarToExactQM31 generatedM31ToExact
    sourceQm31ToModel sourceCm31ToModel
  rw [field.M31_QUARTER]
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext
    · change (536870912 : ModelM31) * 4 = 1
      decide
    · change (0 : ModelM31) = 0
      rfl
  · apply QuadraticAlgebra.ext <;> rfl

private theorem raw_quarter_canonical :
    GeneratedCanonicalM31 field.M31_QUARTER := by
  norm_num [GeneratedCanonicalM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31, field.M31_QUARTER,
    AspisAeneasCM31Multiplicative.m31Modulus]

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do
      let value ← input
      next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

/-- A successful literal decoder call returns canonical coefficients equal to
the maintained reconstruction from the six transmitted parts. -/
theorem decode_compact_relation_polynomial_exact
    (sent : Array RawQM31 6#usize) (runningClaim : RawQM31)
    (polynomial : Array RawQM31 7#usize)
    (sentCanonical : CanonicalRelationRow sent)
    (runningCanonical : GeneratedCanonicalQM31 runningClaim)
    (success :
      v6_transcript.decode_compact_relation_polynomial sent runningClaim =
        ok polynomial) :
    CanonicalArray polynomial ∧
      (fun coefficient =>
        sourceQm31ToModel (exactCoefficients polynomial coefficient)) =
        fun coefficient => relationCoefficient sourceQuarter
          (sourceQm31ToModel (generatedQm31ToExact runningClaim))
          (exactRelationParts sent)
          coefficient := by
  have sent0Canonical : GeneratedCanonicalQM31 sent.val[0]! :=
    sentCanonical 0 (by norm_num)
  have sent0Bang : sent.val[0]! = sent.val[0] := by
    apply List.getElem!_of_getElem?
    simp
  have sent1Bang : sent.val[1]! = sent.val[1] := by
    apply List.getElem!_of_getElem?
    simp
  have sent2Bang : sent.val[2]! = sent.val[2] := by
    apply List.getElem!_of_getElem?
    simp
  have sent3Bang : sent.val[3]! = sent.val[3] := by
    apply List.getElem!_of_getElem?
    simp
  have sent4Bang : sent.val[4]! = sent.val[4] := by
    apply List.getElem!_of_getElem?
    simp
  have sent5Bang : sent.val[5]! = sent.val[5] := by
    apply List.getElem!_of_getElem?
    simp
  have sent0CanonicalGet : GeneratedCanonicalQM31 sent.val[0] := by
    rw [← sent0Bang]
    exact sent0Canonical
  unfold v6_transcript.decode_compact_relation_polynomial at success
  rw [bind_eq_ok_iff] at success
  obtain ⟨q0, q0Read, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨polynomial1, polynomial1Update, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨q1, q1Read, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨polynomial2, polynomial2Update, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨q2, q2Read, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨polynomial3, polynomial3Update, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨q3, q3Read, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨polynomial4, polynomial4Update, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨q4, q4Read, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨polynomial5, polynomial5Update, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨q5, q5Read, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨polynomial6, polynomial6Update, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨scaled, scaledRun, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨q0Again, q0AgainRead, success⟩ := success
  rw [bind_eq_ok_iff] at success
  obtain ⟨missing, missingRun, finalUpdate⟩ := success
  have q0Exact : q0 = sent.val[0] := by
    simpa [Array.index_usize] using q0Read.symm
  have q1Exact : q1 = sent.val[1] := by
    simpa [Array.index_usize] using q1Read.symm
  have q2Exact : q2 = sent.val[2] := by
    simpa [Array.index_usize] using q2Read.symm
  have q3Exact : q3 = sent.val[3] := by
    simpa [Array.index_usize] using q3Read.symm
  have q4Exact : q4 = sent.val[4] := by
    simpa [Array.index_usize] using q4Read.symm
  have q5Exact : q5 = sent.val[5] := by
    simpa [Array.index_usize] using q5Read.symm
  subst q0
  subst q1
  subst q2
  subst q3
  subst q4
  subst q5
  simp [Array.update] at polynomial1Update
  subst polynomial1
  simp [Array.update] at polynomial2Update
  subst polynomial2
  simp [Array.update] at polynomial3Update
  subst polynomial3
  simp [Array.update] at polynomial4Update
  subst polynomial4
  simp [Array.update] at polynomial5Update
  subst polynomial5
  simp [Array.update] at polynomial6Update
  subst polynomial6
  have q0AgainExact : q0Again = sent.val[0] := by
    simpa [Array.index_usize] using q0AgainRead.symm
  subst q0Again
  obtain ⟨scaledExpected, scaledExpectedRun, scaledCanonical, scaledExact⟩ :=
    generated_qm31_mul_m31_corresponds runningClaim field.M31_QUARTER
      runningCanonical raw_quarter_canonical
  rw [scaledRun] at scaledExpectedRun
  cases scaledExpectedRun
  obtain ⟨missingExpected, missingExpectedRun, missingCanonical, missingExact⟩ :=
    generated_qm31_sub_corresponds scaled sent.val[0]
      scaledCanonical sent0CanonicalGet
  rw [missingRun] at missingExpectedRun
  cases missingExpectedRun
  simp [Array.update] at finalUpdate
  subst polynomial
  constructor
  · intro index indexBound
    interval_cases index <;>
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some]
    · simpa only [sent0Bang] using sentCanonical 0 (by norm_num)
    · simpa only [sent1Bang] using sentCanonical 1 (by norm_num)
    · simpa only [sent2Bang] using sentCanonical 2 (by norm_num)
    · simpa only [sent3Bang] using sentCanonical 3 (by norm_num)
    · exact missingCanonical
    · simpa only [sent4Bang] using sentCanonical 4 (by norm_num)
    · simpa only [sent5Bang] using sentCanonical 5 (by norm_num)
  · funext coefficient
    fin_cases coefficient <;>
      simp [exactCoefficients, exactRelationParts, relationCoefficient]
    rw [missingExact, scaledExact]
    simp only [sourceQm31ToModel_sub, sourceQm31ToModel_mul]
    unfold sourceQuarter reconstructedRelationQuartic
    ring

/-- Evaluation of a source exact relation polynomial commutes with the
coordinate ring homomorphism into the maintained K1 field. -/
theorem sourceQm31ToModel_relationPolynomial_eval
    (coefficients : Fin 7 → SourceQM31) (point : SourceQM31) :
    sourceQm31ToModel ((AspisV5RelationSumcheckSoundness.relationPolynomial
      coefficients).eval point) =
      (AspisV5RelationSumcheckSoundness.relationPolynomial
        (fun coefficient => sourceQm31ToModel (coefficients coefficient))).eval
        (sourceQm31ToModel point) := by
  rw [AspisV5RelationSumcheckSoundness.eval_relationPolynomial,
    AspisV5RelationSumcheckSoundness.eval_relationPolynomial]
  change sourceQm31ToModelHom
      (∑ coefficient : Fin 7,
        coefficients coefficient * point ^ coefficient.val) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro coefficient _
  rw [map_mul, map_pow]
  rfl

/-- Decoding followed by the literal generated Horner evaluator is exactly
the maintained relation-round transition. -/
theorem decode_and_evaluate_exact
    (sent : Array RawQM31 6#usize) (runningClaim alpha : RawQM31)
    (polynomial : Array RawQM31 7#usize) (output : RawQM31)
    (sentCanonical : CanonicalRelationRow sent)
    (runningCanonical : GeneratedCanonicalQM31 runningClaim)
    (alphaCanonical : GeneratedCanonicalQM31 alpha)
    (decodeSuccess :
      v6_transcript.decode_compact_relation_polynomial sent runningClaim =
        ok polynomial)
    (evaluateSuccess : sumcheck.evaluate polynomial alpha = ok output) :
    GeneratedCanonicalQM31 output ∧
      sourceQm31ToModel (generatedQm31ToExact output) =
        relationEvaluate sourceQuarter
          (sourceQm31ToModel (generatedQm31ToExact runningClaim))
          (exactRelationParts sent)
          (sourceQm31ToModel (generatedQm31ToExact alpha)) := by
  obtain ⟨polynomialCanonical, coefficientsExact⟩ :=
    decode_compact_relation_polynomial_exact sent runningClaim polynomial
      sentCanonical runningCanonical decodeSuccess
  obtain ⟨outputCanonical, outputExact⟩ :=
    generated_evaluate_success_relationPolynomial polynomial alpha output
      polynomialCanonical alphaCanonical evaluateSuccess
  refine ⟨outputCanonical, ?_⟩
  rw [outputExact, sourceQm31ToModel_relationPolynomial_eval,
    coefficientsExact]
  rw [AspisV5RelationSumcheckSoundness.eval_relationPolynomial]
  rfl

#print axioms sourceQuarter_mul_four
#print axioms decode_compact_relation_polynomial_exact
#print axioms sourceQm31ToModel_relationPolynomial_eval
#print axioms decode_and_evaluate_exact

end V7CallerCurrentReleaseR26RelationDecodeSemantics
