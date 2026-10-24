import S1ExtractedDecodedRoundTotalV1
import SemanticCallSelectedCanonical
set_option autoImplicit false
namespace AspisS1ExtractedRoundChildren
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

/-- Only the alpha coordinate actually read by semantic_value is required. -/
theorem decoded_value_total_selected (r : MainRecord) (offset : Usize)
    (p : Array MainQM 28#usize) (a : Array MainQM 10#usize) (round : Usize)
    (decoded : children.decode 28#usize r offset = ok (.Ok p))
    (hr : round.val < 10)
    (ha : Canonical (a.val[round.val]'(by simpa [a.property] using hr))) :
    ∃ out, children.value p a round = ok out ∧ Canonical out := by
  have hp := decoded_members_canonical _ r offset p decoded
  have hcoeff : ∀ i : Nat, (hi : i < 28) →
      AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
        (genQToProbe ((mainArrayToGen p).val[i]'(by simpa [mainArrayToGen] using hi))) := by
    intro i hi
    have himem := hp (p.val[i]'(by simpa [p.property] using hi)) (List.getElem_mem _)
    simpa only [Canonical, mainArrayToGen, List.getElem_map] using himem
  have halpha : AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
      (genQToProbe ((mainAlphaArrayToGen a).val[round.val]'(by simpa [mainAlphaArrayToGen] using hr))) := by
    simpa only [Canonical, mainAlphaArrayToGen, List.getElem_map] using ha
  obtain ⟨out, call, canon, _⟩ :=
    AspisR1PublicPreparation.RawExtractedSemanticValueLoopV1.semantic_value_refines_polynomial_eval
      (mainArrayToGen p) (mainAlphaArrayToGen a) round hr halpha hcoeff
  refine ⟨genToMain out, ?_, ?_⟩
  · change genResultToMain
      (AspisR1SemanticCallExtraction.r1_semantic.semantic_value_entry
        (mainArrayToGen p) (mainAlphaArrayToGen a) round) = _
    simpa only [AspisR1SemanticCallExtraction.r1_semantic.semantic_value_entry,
      call, genResultToMain, bind_tc_ok]
  · cases out with
    | mk c0 c1 => cases c0; cases c1; exact canon

theorem sampled_canonical {H : Type}
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (self after : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (record : MainRecord) (q : MainQM)
    (sample : AspisR1PublicPreparation.r1_wire.SemanticTranscript.semantic_validated
      D self record = ok (.Ok q, after)) : Canonical q := by
  exact AspisR1PublicPreparation.SemanticCallSelectedCanonical.semantic_success_selected_canonical
    D self after record q sample

/-- At the decode/sample/update boundary used by the caller, both numeric
input ranges are derived from the same concrete calls. No coefficient or
alpha canonicality premise, nor independent value success, remains. These
reached calls and round<10 are explicit; arbitrary whole-stage TOTAL is not
asserted. Unread alpha coordinates may be arbitrary words. -/
theorem decoded_sampled_value_total {H : Type}
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (self after : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (record : MainRecord) (p : Array MainQM 28#usize)
    (beforeAlpha afterAlpha : Array MainQM 10#usize) (round : Usize) (q : MainQM)
    (decoded : children.decode 28#usize record 0#usize = ok (.Ok p))
    (sample : AspisR1PublicPreparation.r1_wire.SemanticTranscript.semantic_validated
      D self record = ok (.Ok q, after))
    (update : Array.update beforeAlpha round q = ok afterAlpha)
    (hr : round.val < 10) :
    ∃ out, children.value p afterAlpha round = ok out ∧ Canonical out := by
  have hq := sampled_canonical D self after record q sample
  apply decoded_value_total_selected record 0#usize p afterAlpha round decoded hr
  unfold Array.update at update
  split at update
  · cases update
  · have same := (Result.ok.inj update).symm
    subst afterAlpha
    simpa [Array.set] using hq

#print axioms decoded_value_total_selected
#print axioms sampled_canonical
#print axioms decoded_sampled_value_total
end AspisS1ExtractedRoundChildren
