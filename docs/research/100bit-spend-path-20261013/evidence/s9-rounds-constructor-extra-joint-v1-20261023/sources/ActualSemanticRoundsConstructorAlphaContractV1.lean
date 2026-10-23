import ActualSemanticRoundsConstructorAlphaV1
import ActualSemanticRoundsCanonicalV1
import S9ActualWeightsNewExtraCurrentCanonicalV3
import S9CandidateFoldMapPrimitivesV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1ActualSemanticRoundsConstructorAlphaContractV1
open AspisR1ActualSemanticRoundsConstructorAlphaV1

/-- A successful Actual-only ten-round call supplies the exact nested mapped
alpha-read canonicality contract expected by constructor v3. The two carrier
maps preserve the four U32 coordinates; source caller emission remains a
separate boundary. -/
theorem actual_rounds_success_constructor_alpha_contract {H : Type}
    (B : AspisR1ActualSemanticRoundSourceModelV1.Hooks)
    (D : AspisR1ActualSemanticRoundCutV1.aspis_core.digest.Digest32 H)
    (pre : AspisR1ActualSemanticRoundCutV1.r1_wire.Prefix)
    (self after : AspisR1ActualSemanticRoundCutV1.r1_wire.SemanticTranscript H)
    (running : RoundQM) (alpha : Array RoundQM 10#usize)
    (hrounds : AspisR1ActualSemanticRoundsCanonicalV1.actualSourceRounds
      B D pre self = .ok (.Ok (running, alpha, after))) :
    ∀ (i : Usize) (q : AspisR1S9PairCallerStepV1.field.QM31),
      Array.index_usize
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1S9ActualWeightsNewExtraCurrentCanonicalV3.candidateToPairQM
          (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray roundToWeightsQM alpha)) i = .ok q →
      AspisR1CurrentWide.Proof.CanonicalQM
        (AspisR1S9HelperP6PowerSemanticsV1.helperToCurrentQM
          (AspisR1S9PairCallerStepV1.toP6Q q)) := by
  intro i q hread
  have hroundCanonical :=
    AspisR1ActualSemanticRoundsCanonicalV1.actual_source_rounds_success_all_alpha_reads_canonical
      B D pre self after running alpha hrounds
  have houter := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result
    AspisR1S9ActualWeightsNewExtraCurrentCanonicalV3.candidateToPairQM
    (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray roundToWeightsQM alpha) i
  rw [hread] at houter
  cases hinter : Array.index_usize
      (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray roundToWeightsQM alpha) i with
  | ok wq =>
      rw [hinter] at houter
      change Result.ok
        (AspisR1S9ActualWeightsNewExtraCurrentCanonicalV3.candidateToPairQM wq) = .ok q at houter
      have hq : AspisR1S9ActualWeightsNewExtraCurrentCanonicalV3.candidateToPairQM wq = q :=
        Result.ok.inj houter
      subst q
      exact mapped_alpha_reads_constructor_canonical alpha hroundCanonical i wq hinter
  | fail e =>
      rw [hinter] at houter
      change Result.fail e = .ok q at houter
      cases houter
  | div =>
      rw [hinter] at houter
      change Result.div = .ok q at houter
      cases houter

#print axioms actual_rounds_success_constructor_alpha_contract
end AspisR1ActualSemanticRoundsConstructorAlphaContractV1
