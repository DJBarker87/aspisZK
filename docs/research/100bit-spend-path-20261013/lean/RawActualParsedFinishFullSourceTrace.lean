import RawActualParsedFinishWideEndpoint
import ActualMainMaskR0PValue
import RawBeginAnnotatedFullTrace
import RawActualParsedFinishR0PChain

/-! Actual strict parsing, begin and finish imply a semantic-view chain whose
masked endpoint uses the existing R0P selected mask definition. Claims,
array-library and public-terminal implementation obligations remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawActualParsedFinishFullSourceTrace
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
open AspisR1PublicPreparation.ActualFinishConcreteArithmeticBoundary
open AspisR1PublicPreparation.ActualMainMaskPopulatedBridge
open AspisR1PublicPreparation.RawActualAnnotatedPolynomialRun
open AspisR1PublicPreparation.RawActualParsedSemanticChain
open AspisR1PublicPreparation.RawActualParsedSemanticViewChain

open AspisR1PublicPreparation.RawActualParsedFinishR0PChain
 theorem parsed_finish_full_source_trace
    (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (pre : r1_wire.Prefix)
    (hparse : PrefixAdapter.parseAccepted bytes = .ok (.Ok pre))
    (beforeBegin before : r1_wire.SemanticTranscript H)
    (challenges : r1_wire.Challenges)
    (hbegin : r1_wire.begin D pre beforeBegin = .ok (.Ok challenges,before))
    (obs : Option (verifier.Phase → Result Unit))
    (out : r1_semantic.Verified H)
    (hfinish : FinishModel.finish RawActualSemanticRoundCanonicality.actualRoundBoundaries
      (withConcreteArithmetic B) D pub pre before challenges obs = .ok (.Ok out)) :
    ∃ running afterRounds terminal mask16 mask10 claim0 claim27 extra28,
      ∃ values : AspisR1.SemanticPrefixCodec.Full,
      ∃ initial : RawSemanticFieldOwnerAdapter.MainQM,
      ∃ entries : List (RoundEvidence D pre), ∃ cs : List (SourceFull25.Call D pre),
      RoundModel.rounds RawActualSemanticRoundCanonicality.actualRoundBoundaries
        D pre before = .ok (.Ok (running,out.alpha,afterRounds)) ∧
      AspisR1.SemanticPrefixCodec.encodeFull values = PrefixAdapter.completedRecords pre ∧
      AnnotatedRun D pre SemanticRoundsCheckedTrace.schedule
        (initial, Array.repeat 10#usize aspis_core.field.QM31.ZERO, before)
        (running,out.alpha,afterRounds) entries ∧
      entries.map RoundEvidence.q = out.alpha.val ∧
      B.terminal pub out.claims out.alpha challenges = .ok (.Ok terminal) ∧
      B.fromFn 16#usize (FinishModel.closureFn9 D) out.claims = .ok mask16 ∧
      B.fromFn 10#usize (FinishModel.closureFn5 D) out.claims = .ok mask10 ∧
      Array.index_usize out.claims 0#usize = .ok claim0 ∧
      Array.index_usize claim0 27#usize = .ok claim27 ∧
      Array.index_usize out.extra 28#usize = .ok extra28 ∧
      SourceFull25.Trace D pre beforeBegin afterRounds cs ∧
      cs.map (fun c => c.row.val) = List.range 25 ∧
      cs.map SourceFull25.Call.q = BeginCalls.challengeList challenges ++ out.alpha.val ∧
      SourceFull25.rawFrames cs = PrefixAdapter.completedRecords pre ∧
      AspisR1.SemanticPrefixCodec.decodeFrom 0 (SourceFull25.rawFrames cs) =
        some (AspisR1.SemanticPrefixCodec.entriesOf values) ∧
      (∀ c ∈ cs, (SourceDigestAddresses.rawBytes c.record.framed).length ≤ 901) ∧
      (CanonicalArray mask16 → CanonicalArray mask10 →
        Canonical (mainToProbe claim27) → Canonical (mainToProbe terminal) →
        RawGenericPolynomialSumcheckChain.Chain
          (AspisR1.SemanticPayloadView.claimAt14 values)
          (r0pEndpoint mask16 mask10 claim27 out.alpha challenges.eta terminal extra28)
          (viewPairs D pre values entries)) := by
  obtain ⟨running,afterRounds,terminal,mask16,mask10,claim0,claim27,extra28,
      values,initial,entries,hrounds,hfull,hrun,hqs,hterminal,
      hm16,hm10,hc0,hc27,hextra,hchain⟩ :=
    parsed_finish_r0p_chain B D pub bytes pre hparse beforeBegin before challenges hbegin obs out hfinish
  obtain ⟨cs,htrace,hrows,hcalls,hframes,hdecoded,hbounds⟩ :=
    RawBeginAnnotatedFullTrace.begin_annotated_full_trace D bytes pre hparse
      beforeBegin before challenges hbegin initial
      (Array.repeat 10#usize aspis_core.field.QM31.ZERO)
      (running,out.alpha,afterRounds) entries hrun values hfull
  refine ⟨running,afterRounds,terminal,mask16,mask10,claim0,claim27,extra28,
    values,initial,entries,cs,hrounds,hfull,hrun,hqs,hterminal,
    hm16,hm10,hc0,hc27,hextra,htrace,hrows,?_,hframes,hdecoded,hbounds,hchain⟩
  simpa only [hqs] using hcalls

#print axioms parsed_finish_full_source_trace
end AspisR1PublicPreparation.RawActualParsedFinishFullSourceTrace
end
