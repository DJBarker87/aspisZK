import RawSourceLiteralFull25Prefix
import RawBeginAnnotatedFullTrace

/-! Couple actual begin and the same annotated polynomial rounds to one literal
sampler prefix, preserving the exact source challenge list and arithmetic alpha.
The public-byte and root representation links remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawBeginAnnotatedLiteralPrefix
open Aeneas Aeneas.Std Result
open AspisR1
open AspisR1PublicPreparation.RawActualAnnotatedPolynomialRun
open AspisR1PublicPreparation.SourceDigestAddresses
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.SqueezeOracleBridge
open FS FS2 FS2.Duplex

structure Coupled {H : Type} (D : aspis_core.Digest32 H)
    (pre : r1_wire.Prefix) (before after : r1_wire.SemanticTranscript H)
    (qs : List aspis_core.field.QM31) (oracleInput : Slice U8)
    (root : TranscriptStep.Bytes32) (P : LiteralTranscript.Prefix)
    (c1 : State) (word : LiteralTranscript.C1Word) where
  length : U32
  first : SourceFull25.Call D pre
  tail : List (SourceFull25.Call D pre)
  boundTail : ∀ d ∈ tail,
    (rawBytes d.record.framed).length ≤ SelectedTranscriptParams.params.D
  trace : SourceFull25.Trace D pre before after (first :: tail)
  rows : (first :: tail).map (fun d => d.row.val) = List.range 25
  challenges : (first :: tail).map SourceFull25.Call.q = qs
  frames : SourceFull25.rawFrames (first :: tail) = PrefixAdapter.completedRecords pre
  firstEmpty : rawBytes first.record.framed = PublicInitFrame.emptyRecord
  initial : let Hbytes := @SourceLiteralFull25Prefix.sourceOracleBytes H D
      before.hash oracleInput root length
    SourceLiteralFull25Prefix.initialPostPrefix Hbytes P c1 word =
      SourceLiteralFull25Prefix.sourceInitialPostPrefix P c1 word first
  literal : let Hbytes := @SourceLiteralFull25Prefix.sourceOracleBytes H D
      before.hash oracleInput root length
    let Pnext := SourceLiteralFull25Prefix.initialPostPrefix Hbytes P c1 word
    SourceLiteralTraceLift.literalPrefix Hbytes 1 Pnext tail boundTail =
      SourceLiteralTraceLift.sourcePrefix 1 Pnext tail boundTail
  state : let Hbytes := @SourceLiteralFull25Prefix.sourceOracleBytes H D
      before.hash oracleInput root length
    let Pnext := SourceLiteralFull25Prefix.initialPostPrefix Hbytes P c1 word
    UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix
        (SourceLiteralTraceLift.sourcePrefix 1 Pnext tail boundTail)) =
      decodeState after.state

theorem actual_begin_and_rounds_coupled {H : Type} (D : aspis_core.Digest32 H)
    (bytes : Slice U8) (pre : r1_wire.Prefix)
    (hparse : PrefixAdapter.parseAccepted bytes = .ok (.Ok pre))
    (beforeBegin before : r1_wire.SemanticTranscript H)
    (challenges : r1_wire.Challenges)
    (hbegin : r1_wire.begin D pre beforeBegin = .ok (.Ok challenges,before))
    (initial : MainQM) (initialAlpha : Array MainQM 10#usize)
    (final : Outcome H) (entries : List (RoundEvidence D pre))
    (run : AnnotatedRun D pre SemanticRoundsCheckedTrace.schedule
      (initial,initialAlpha,before) final entries)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (oracleInput : Slice U8) (root : TranscriptStep.Bytes32)
    (hpublic : r1_semantic.public_transcript D pub beforeBegin.hash root =
      .ok (.Ok beforeBegin))
    (P : LiteralTranscript.Prefix) (c1 : State) (word : LiteralTranscript.C1Word)
    (hPround : P.round = 0)
    (hpublicBytes : ∀ encoded : alloc.vec.Vec U8,
      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes pub =
        .ok (.Ok encoded) → P.statement.pubBytes = rawBytes (alloc.vec.Vec.deref encoded))
    (horacleInput : ∀ encoded : alloc.vec.Vec U8,
      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes pub =
        .ok (.Ok encoded) → oracleInput = alloc.vec.Vec.deref encoded)
    (hroot : c1 = decodeState root) :
    Nonempty (Coupled D pre beforeBegin final.2.2
      (BeginCalls.challengeList challenges ++ entries.map RoundEvidence.q)
      oracleInput root P c1 word) := by
  obtain ⟨qs,hbeginRun,hbeginQs⟩ :=
    BeginCalls.begin_success D pre beforeBegin before challenges hbegin
  have hroundRun := RawAnnotatedSourceTrace.annotated_semantic_run D pre
    SemanticRoundsCheckedTrace.schedule (initial,initialAlpha,before) final entries run
  have hrun := RawBeginAnnotatedFullTrace.semantic_run_append D pre hbeginRun hroundRun
  have hrows : (BeginCalls.rows ++ SemanticRoundsCheckedTrace.schedule.map Prod.snd).map
      (fun row => row.val) = List.range 25 := by rfl
  obtain ⟨encoded,length,tail,values,c,boundTail,henc,hinput,htrace,htailTrace,
      hcallRows,hqs,hframes,hdecode,hbounds,hempty,hrest⟩ :=
    SourceLiteralFull25Prefix.full25_initial_and_positive_prefix bytes hparse
      hrun hrows pub oracleInput root hpublic P c1 word hPround
      hpublicBytes horacleInput hroot
  refine ⟨⟨length,c,tail,boundTail,htrace,hcallRows,?_,hframes,hempty,
    hrest.2.1,hrest.2.2.1,hrest.2.2.2⟩⟩
  simpa only [hbeginQs] using hqs

#print axioms actual_begin_and_rounds_coupled
end AspisR1PublicPreparation.RawBeginAnnotatedLiteralPrefix
end
