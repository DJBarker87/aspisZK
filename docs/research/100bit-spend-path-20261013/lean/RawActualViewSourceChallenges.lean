import RawAnnotatedSourceTrace
import RawSourceLiteralTraceLift
import RawActualParsedSemanticViewChain

/-! The arithmetic chain and source/literal sampler use one actual challenge
list, obtained from the very same annotated source run. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawActualViewSourceChallenges
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawActualAnnotatedPolynomialRun
open AspisR1PublicPreparation.RawActualParsedSemanticChain
open AspisR1PublicPreparation.RawActualParsedSemanticViewChain

 theorem source_challenges_eq_viewPairs {H : Type}
    (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix)
    (values : AspisR1.SemanticPrefixCodec.Full)
    (entries : List (RoundEvidence D pre)) (cs : List (SourceFull25.Call D pre))
    (hqs : cs.map SourceFull25.Call.q = entries.map RoundEvidence.q) :
    cs.map SourceLiteralTraceLift.sourceChallenge =
      (viewPairs D pre values entries).map Prod.snd := by
  have h := congrArg (fun qs : List MainQM =>
    qs.map (fun q => algebraMap E W (DecodeMain q))) hqs
  rw [viewPairs, List.map_map]
  change cs.map (fun c => algebraMap E W (DecodeMain c.q)) =
    entries.map (fun e => algebraMap E W (DecodeMain e.q))
  simpa only [List.map_map, Function.comp_def] using h

 theorem parsed_rounds_chain_source_trace {H : Type}
    (bytes : Slice U8) (pre : r1_wire.Prefix)
    (hparse : PrefixAdapter.parseAccepted bytes = .ok (.Ok pre))
    (D : aspis_core.Digest32 H) (self afterRounds : r1_wire.SemanticTranscript H)
    (running : MainQM) (alpha : Array MainQM 10#usize)
    (hrounds : RoundModel.rounds
      RawActualSemanticRoundCanonicality.actualRoundBoundaries D pre self =
      .ok (.Ok (running, alpha, afterRounds))) :
    ∃ values : AspisR1.SemanticPrefixCodec.Full, ∃ initial : MainQM,
    ∃ entries : List (RoundEvidence D pre), ∃ cs : List (SourceFull25.Call D pre),
      AspisR1.SemanticPrefixCodec.encodeFull values = PrefixAdapter.completedRecords pre ∧
      AnnotatedRun D pre SemanticRoundsCheckedTrace.schedule
        (initial, Array.repeat 10#usize aspis_core.field.QM31.ZERO, self)
        (running, alpha, afterRounds) entries ∧
      SourceFull25.Trace D pre self afterRounds cs ∧
      cs.map SourceFull25.Call.row = SemanticRoundsCheckedTrace.schedule.map Prod.snd ∧
      cs.map SourceFull25.Call.q = alpha.val ∧
      cs.map SourceLiteralTraceLift.sourceChallenge =
        (viewPairs D pre values entries).map Prod.snd ∧
      RawGenericPolynomialSumcheckChain.Chain
        (AspisR1.SemanticPayloadView.claimAt14 values)
        (algebraMap K W (DecodeMain running)) (viewPairs D pre values entries) := by
  obtain ⟨values, initial, entries, hfull, hrun, hqs, hchain⟩ :=
    parsed_rounds_semantic_view_chain bytes pre hparse D self afterRounds running alpha hrounds
  obtain ⟨cs, htrace, hrows, hcalls, hframes⟩ :=
    RawAnnotatedSourceTrace.annotated_source_trace D pre _ _ _ entries hrun
  exact ⟨values, initial, entries, cs, hfull, hrun, htrace, hrows,
    hcalls.trans hqs, source_challenges_eq_viewPairs D pre values entries cs hcalls, hchain⟩

#print axioms source_challenges_eq_viewPairs
#print axioms parsed_rounds_chain_source_trace
end AspisR1PublicPreparation.RawActualViewSourceChallenges
end
