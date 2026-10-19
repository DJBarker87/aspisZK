import RawActualParsedFinishFullSourceTrace
import RawBeginAnnotatedLiteralPrefix

/-! Actual finish reaches the existing R0P arithmetic chain and a coupled
literal first25 prefix with exactly the begin challenges followed by its own
polynomial alpha values. Public and unfinished caller refinements remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawActualParsedFinishLiteralPrefix
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
open AspisR1PublicPreparation.ActualFinishConcreteArithmeticBoundary
open AspisR1PublicPreparation.ActualMainMaskPopulatedBridge
open AspisR1PublicPreparation.RawActualAnnotatedPolynomialRun
open AspisR1PublicPreparation.RawActualParsedSemanticChain
open AspisR1PublicPreparation.RawActualParsedSemanticViewChain

open AspisR1PublicPreparation.RawActualParsedFinishR0PChain
 theorem parsed_finish_literal_prefix
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
      (withConcreteArithmetic B) D pub pre before challenges obs = .ok (.Ok out))
    (oracleInput : Slice U8) (root : TranscriptStep.Bytes32)
    (hpublic : r1_semantic.public_transcript D pub beforeBegin.hash root = .ok (.Ok beforeBegin))
    (P : AspisR1.LiteralTranscript.Prefix)
    (c1 : State) (word : AspisR1.LiteralTranscript.C1Word)
    (hPround : P.round = 0)
    (hpublicBytes : ∀ encoded : alloc.vec.Vec U8,
      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes pub = .ok (.Ok encoded) →
      P.statement.pubBytes = SourceDigestAddresses.rawBytes (alloc.vec.Vec.deref encoded))
    (horacleInput : ∀ encoded : alloc.vec.Vec U8,
      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes pub = .ok (.Ok encoded) →
      oracleInput = alloc.vec.Vec.deref encoded)
    (hroot : c1 = decodeState root) :
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
      Nonempty (RawBeginAnnotatedLiteralPrefix.Coupled D pre beforeBegin afterRounds
        (BeginCalls.challengeList challenges ++ out.alpha.val) oracleInput root P c1 word) ∧
      (CanonicalArray mask16 → CanonicalArray mask10 →
        Canonical (mainToProbe claim27) → Canonical (mainToProbe terminal) →
        RawGenericPolynomialSumcheckChain.Chain
          (AspisR1.SemanticPayloadView.claimAt14 values)
          (r0pEndpoint mask16 mask10 claim27 out.alpha challenges.eta terminal extra28)
          (viewPairs D pre values entries)) := by
  obtain ⟨running,afterRounds,terminal,mask16,mask10,claim0,claim27,extra28,
      values,initial,entries,cs,hrounds,hfull,hrun,hqs,hterminal,
      hm16,hm10,hc0,hc27,hextra,htrace,hrows,hcalls,hframes,hdecoded,hbounds,hchain⟩ :=
    RawActualParsedFinishFullSourceTrace.parsed_finish_full_source_trace
      B D pub bytes pre hparse beforeBegin before challenges hbegin obs out hfinish
  have hcoupled := RawBeginAnnotatedLiteralPrefix.actual_begin_and_rounds_coupled
    D bytes pre hparse beforeBegin before challenges hbegin initial
    (Array.repeat 10#usize aspis_core.field.QM31.ZERO)
    (running,out.alpha,afterRounds) entries hrun pub oracleInput root hpublic
    P c1 word hPround hpublicBytes horacleInput hroot
  refine ⟨running,afterRounds,terminal,mask16,mask10,claim0,claim27,extra28,
    values,initial,entries,cs,hrounds,hfull,hrun,hqs,hterminal,
    hm16,hm10,hc0,hc27,hextra,htrace,hrows,hcalls,hframes,hdecoded,hbounds,?_,hchain⟩
  simpa only [hqs] using hcoupled

#print axioms parsed_finish_literal_prefix
end AspisR1PublicPreparation.RawActualParsedFinishLiteralPrefix
end
