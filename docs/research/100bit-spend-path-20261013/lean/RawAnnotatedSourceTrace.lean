import RawSourceChallengeCarrier
import ExtractedSourceFull25Frames

/-! Construct the digest-call trace from the same annotated arithmetic run;
no independently selected challenge sequence is paired with its polynomials. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawAnnotatedSourceTrace
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawActualAnnotatedPolynomialRun

 theorem annotated_semantic_run {H : Type} (D : aspis_core.Digest32 H)
    (pre : r1_wire.Prefix) (events : List (Usize × U8))
    (initial final : Outcome H) (entries : List (RoundEvidence D pre))
    (run : AnnotatedRun D pre events initial final entries) :
    BeginCalls.SemanticRun D pre (events.map Prod.snd)
      initial.2.2 final.2.2 (entries.map RoundEvidence.q) := by
  induction run with
  | nil out => exact .nil _
  | @cons entry events final entries tail ih =>
    exact .cons entry.recordOk entry.semanticOk ih

 theorem annotated_source_trace {H : Type} (D : aspis_core.Digest32 H)
    (pre : r1_wire.Prefix) (events : List (Usize × U8))
    (initial final : Outcome H) (entries : List (RoundEvidence D pre))
    (run : AnnotatedRun D pre events initial final entries) :
    ∃ cs : List (SourceFull25.Call D pre),
      SourceFull25.Trace D pre initial.2.2 final.2.2 cs ∧
      cs.map SourceFull25.Call.row = events.map Prod.snd ∧
      cs.map SourceFull25.Call.q = entries.map RoundEvidence.q ∧
      cs.map (fun c => c.record.framed) =
        (events.map Prod.snd).filterMap (fun row => pre.records.val[row.val]?) := by
  obtain ⟨cs, htrace, hrows, hqs⟩ := SourceFull25.calls_of_run D pre
    (annotated_semantic_run D pre events initial final entries run)
  refine ⟨cs, htrace, hrows, hqs, ?_⟩
  rw [SourceFull25.frames_eq_slots, hrows]

#print axioms annotated_semantic_run
#print axioms annotated_source_trace
end AspisR1PublicPreparation.RawAnnotatedSourceTrace
end
