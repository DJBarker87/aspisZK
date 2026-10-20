import RawTx1DigestLog
import RawSourceGlobalOracleFull25

/-! Discharge the old global-log premises for a constructed conditional tx1
log. Full transaction inventory and backend realization remain named premises. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.Tx1GlobalOracleFull25
open Aeneas Aeneas.Std Result AspisR1
open AspisR1.LiteralTranscript AspisR1.SelectedTranscriptParams AspisR1.TranscriptView
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.SqueezeOracleBridge
open FS FS2 FS2.Duplex
open SourceDigestAddresses SourceDigestLog SourceGlobalOracleInitial Tx1DigestLog

theorem full25_with_tx1_log
    {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    {before after : r1_wire.SemanticTranscript Hash}
    {pub : pool_v1.pair_forest_semantic_terminal.r0.Public}
    {root : TranscriptStep.Bytes32}
    (init : PublicInitCall D pub root before)
    (c : SourceFull25.Call D pre) (tail : List (SourceFull25.Call D pre))
    (run : SourceFull25.Trace D pre before after (c :: tail))
    (hrows : (c :: tail).map (fun d => d.row.val) = List.range 25)
    (values : SemanticPrefixCodec.Full)
    (hdecode : SemanticPrefixCodec.decodeFrom 0 (SourceFull25.rawFrames (c :: tail)) =
      some (SemanticPrefixCodec.entriesOf values))
    (bound : ∀ d ∈ c :: tail,
      (rawBytes d.record.framed).length ≤ SelectedTranscriptParams.params.D)
    (suffix rest : List (Bytes × State))
    (hsuffix : ∀ q ∈ suffix, ActualPair D q)
    (hrest : ∀ q ∈ rest, ActualPair D q)
    (Hbytes : Bytes → State) (hbackend : ByteOracleBackend D Hbytes)
    (P : LiteralTranscript.Prefix) (c1 : State) (word : LiteralTranscript.C1Word)
    (hPround : P.round = 0)
    (hpublicBytes : P.statement.pubBytes = rawBytes (alloc.vec.Vec.deref init.encoded))
    (hroot : c1 = decodeState root) :
    ∃ boundTail : ∀ d ∈ tail,
        (rawBytes d.record.framed).length ≤ SelectedTranscriptParams.params.D,
      rawBytes c.record.framed = PublicInitFrame.emptyRecord ∧
      let Pnext := SourceGlobalOracleFull25.initialPostPrefix Hbytes P c1 word
      Pnext.round = 1 ∧
      Pnext = SourceGlobalOracleFull25.sourceInitialPostPrefix P c1 word c ∧
      SourceLiteralTraceLift.literalPrefix Hbytes 1 Pnext tail boundTail =
        SourceLiteralTraceLift.sourcePrefix 1 Pnext tail boundTail ∧
      AspisR1.UnifiedSampler.stateOf SelectedTranscriptParams.params
        (LiteralTranscript.erasePrefix
          (SourceLiteralTraceLift.sourcePrefix 1 Pnext tail boundTail)) =
        decodeState after.state := by
  exact SourceGlobalOracleFull25.full25_initial_and_positive_prefix init c tail run
    hrows values hdecode bound Hbytes (log init (c :: tail) suffix rest)
    (prefix_contained init (c :: tail) suffix rest)
    (log_consistent init (c :: tail) suffix rest hsuffix hrest Hbytes hbackend)
    P c1 word hPround hpublicBytes hroot

#print axioms full25_with_tx1_log
end AspisR1PublicPreparation.Tx1GlobalOracleFull25
end
