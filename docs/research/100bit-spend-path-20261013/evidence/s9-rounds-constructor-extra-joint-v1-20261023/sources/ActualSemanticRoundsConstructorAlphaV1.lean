import ActualSemanticRoundSameRunAlphaCanonicalV1
import S9ActualWeightsNewExtraCurrentCanonicalV3
import S9CandidateFoldMapPrimitivesV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1ActualSemanticRoundsConstructorAlphaV1

abbrev RoundQM := AspisR1ActualSemanticRoundCutV1.aspis_core.field.QM31
abbrev WeightsQM := AspisR1S9ActualWeightsNewBoxNewV3.field.QM31

/-- Copy the four source-QM coordinates into the constructor's nominal QM type. -/
def roundToWeightsQM (q : RoundQM) : WeightsQM :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩

/-- The actual-round canonical predicate and the constructor's selected-P6
canonical predicate describe the same four U32 coordinates. -/
theorem round_value_canonical_for_weights (q : RoundQM)
    (h : AspisR1.ExtractedQM31SamplerCarrier.CurrentCanonicalQM
      (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
        (AspisR1PublicPreparation.SamplerTransport.toOld
          (AspisR1ActualSamplerDigitWholeMapV1.toPublicQM q)))) :
    AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9ActualWeightsNewExtraCurrentCanonicalV3.candidateToCurrentQM
        (roundToWeightsQM q)) := by
  change
    ((q.c0.a.val < AspisR1.ExtractedCurrentTowerAdd.P ∧
      q.c0.b.val < AspisR1.ExtractedCurrentTowerAdd.P) ∧
     (q.c1.a.val < AspisR1.ExtractedCurrentTowerAdd.P ∧
      q.c1.b.val < AspisR1.ExtractedCurrentTowerAdd.P)) at h
  change
    ((q.c0.a.val < AspisR1.ExtractedCurrentTowerAdd.P ∧
      q.c0.b.val < AspisR1.ExtractedCurrentTowerAdd.P) ∧
     (q.c1.a.val < AspisR1.ExtractedCurrentTowerAdd.P ∧
      q.c1.b.val < AspisR1.ExtractedCurrentTowerAdd.P))
  exact h

/-- Canonicality of every successful read from the mapped actual alpha array
transfers to the exact carrier contract consumed by constructor v3. This is a
nominal-coordinate bridge only; it makes no claim about caller extraction. -/
theorem mapped_alpha_reads_constructor_canonical
    (alpha : Array RoundQM 10#usize)
    (halpha : ∀ (i : Usize) (q : RoundQM),
      Array.index_usize alpha i = .ok q →
      AspisR1.ExtractedQM31SamplerCarrier.CurrentCanonicalQM
        (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
          (AspisR1PublicPreparation.SamplerTransport.toOld
            (AspisR1ActualSamplerDigitWholeMapV1.toPublicQM q)))) :
    ∀ (i : Usize) (q : WeightsQM),
      Array.index_usize
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray roundToWeightsQM alpha) i = .ok q →
      AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9ActualWeightsNewExtraCurrentCanonicalV3.candidateToCurrentQM q) := by
  intro i q hread
  have hm := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result
    roundToWeightsQM alpha i
  rw [hread] at hm
  cases hi : Array.index_usize alpha i with
  | ok x =>
      rw [hi] at hm
      change Result.ok (roundToWeightsQM x) = .ok q at hm
      have hq : roundToWeightsQM x = q := Result.ok.inj hm
      subst q
      exact round_value_canonical_for_weights x (halpha i x hi)
  | fail e =>
      rw [hi] at hm
      change Result.fail e = .ok q at hm
      cases hm
  | div =>
      rw [hi] at hm
      change Result.div = .ok q at hm
      cases hm

#print axioms round_value_canonical_for_weights
#print axioms mapped_alpha_reads_constructor_canonical
end AspisR1ActualSemanticRoundsConstructorAlphaV1
