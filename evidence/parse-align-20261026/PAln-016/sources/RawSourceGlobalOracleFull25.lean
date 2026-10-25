import RawSourceGlobalOracleTrace
import RawSourceGlobalOracleInitial
import RawSourceLiteralInitialCall

/-! One chosen actual initializer and full25 source trace coupled to the same
byte oracle. The actual log embedding remains explicit; no all-address equality
with a separately constructed source oracle is needed. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.SourceGlobalOracleFull25
open Aeneas Aeneas.Std Result
open AspisR1 AspisR1.LiteralTranscript AspisR1.SelectedTranscriptParams AspisR1.TranscriptView
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.SqueezeOracleBridge
open FS FS2 FS2.Duplex
open AspisR1PublicPreparation.SourceDigestAddresses
open SourceDigestLog SourceGlobalOracleInitial
def initialPostPrefix (Hbytes : Bytes → State)
    (P : LiteralTranscript.Prefix) (c1 : State) (word : LiteralTranscript.C1Word) :
    LiteralTranscript.Prefix :=
  P.ext (.initial c1 word)
    (eval (fun a : Addr SelectedTranscriptParams.L => Hbytes a.toBytes)
      (LiteralTranscript.samp 0 P (.initial c1 word)).toProgram).2

def sourceInitialPostPrefix {Hash : Type} {D : aspis_core.Digest32 Hash}
    {pre : r1_wire.Prefix} (P : LiteralTranscript.Prefix)
    (c1 : State) (word : LiteralTranscript.C1Word)
    (c : SourceFull25.Call D pre) : LiteralTranscript.Prefix :=
  P.ext (.initial c1 word)
    (.ordinary (SourceLiteralTraceLift.sourceChallenge c), decodeState c.after.state)


theorem full25_initial_and_positive_prefix
    {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    {before after : r1_wire.SemanticTranscript Hash}
    {pubInput : pool_v1.pair_forest_semantic_terminal.r0.Public}
    {root : TranscriptStep.Bytes32}
    (init : PublicInitCall D pubInput root before)
    (c : SourceFull25.Call D pre) (tail : List (SourceFull25.Call D pre))
    (run : SourceFull25.Trace D pre before after (c :: tail))
    (hrows : (c :: tail).map (fun d => d.row.val) = List.range 25)
    (values : SemanticPrefixCodec.Full)
    (hdecode : SemanticPrefixCodec.decodeFrom 0 (SourceFull25.rawFrames (c :: tail)) =
      some (SemanticPrefixCodec.entriesOf values))
    (bound : ∀ d ∈ c :: tail,
      (rawBytes d.record.framed).length ≤ SelectedTranscriptParams.params.D)
    (Hbytes : Bytes → State) (tr : List (Bytes × State))
    (hsource : initPair init :: sourceLog (c :: tail) ⊆ tr)
    (hcons : ∀ q ∈ tr, q.2 = Hbytes q.1)
    (P : LiteralTranscript.Prefix) (c1 : State) (word : LiteralTranscript.C1Word)
    (hPround : P.round = 0)
    (hpublicBytes : P.statement.pubBytes = rawBytes (alloc.vec.Vec.deref init.encoded))
    (hroot : c1 = decodeState root) :
    ∃ boundTail : ∀ d ∈ tail,
        (rawBytes d.record.framed).length ≤ SelectedTranscriptParams.params.D,
      rawBytes c.record.framed = PublicInitFrame.emptyRecord ∧
      let Pnext := initialPostPrefix Hbytes P c1 word
      Pnext.round = 1 ∧
      Pnext = sourceInitialPostPrefix P c1 word c ∧
      SourceLiteralTraceLift.literalPrefix Hbytes 1 Pnext tail boundTail =
        SourceLiteralTraceLift.sourcePrefix 1 Pnext tail boundTail ∧
      AspisR1.UnifiedSampler.stateOf SelectedTranscriptParams.params
        (LiteralTranscript.erasePrefix
          (SourceLiteralTraceLift.sourcePrefix 1 Pnext tail boundTail)) =
        decodeState after.state := by
  have hsourceRows : sourceLog (c :: tail) ⊆ tr := by
    intro q hq
    exact hsource (List.mem_cons_of_mem _ hq)
  have hinitState := initializer_state_from_log init Hbytes tr
    (hsource (List.mem_cons_self)) hcons P c1 hpublicBytes hroot
  have hbefore : c.before = before := by cases run; rfl
  have hinitCall : decodeState c.before.state = Hbytes
      (PublicInitFrame.addr P.statement.pubBytes P.statement.initFits c1).toBytes := by
    rw [hbefore]
    exact hinitState
  have hrow : c.row.val = 0 := by
    have hh := congrArg (fun xs : List Nat => xs[0]?) hrows
    simpa using hh
  have hempty := SourceLiteralInitialCall.first_framed_empty c tail values hdecode
  have hsim' := SourceGlobalOracleInitial.call_simulates_literal_initial
    (c :: tail) c (by simp) Hbytes tr hsourceRows hcons bound hrow P c1 word hinitCall hempty
  let Pnext := initialPostPrefix Hbytes P c1 word
  have hpair :
      (eval (fun a : Addr SelectedTranscriptParams.L => Hbytes a.toBytes)
        (LiteralTranscript.samp 0 P (.initial c1 word)).toProgram).2 =
      (Value.ordinary (SourceLiteralTraceLift.sourceChallenge c),
        decodeState c.after.state) := by
    apply Prod.ext
    · exact hsim'.1.symm
    · exact hsim'.2.symm
  have hpost : Pnext = sourceInitialPostPrefix P c1 word c := by
    dsimp [Pnext, initialPostPrefix, sourceInitialPostPrefix]
    exact congrArg (fun ch => P.ext (.initial c1 word) ch) hpair
  have hstate : AspisR1.UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix Pnext) = decodeState c.after.state := by
    calc
      AspisR1.UnifiedSampler.stateOf SelectedTranscriptParams.params
          (LiteralTranscript.erasePrefix Pnext) =
        (eval (fun a : Addr SelectedTranscriptParams.L => Hbytes a.toBytes)
          (LiteralTranscript.samp 0 P (.initial c1 word)).toProgram).2.2 := by
            dsimp [Pnext, initialPostPrefix]
            simp only [LiteralTranscript.erasePrefix_ext,
              AspisR1.UnifiedSampler.stateOf_ext]
      _ = decodeState c.after.state := hsim'.2.symm
  have hboundTail : ∀ d ∈ tail,
      (rawBytes d.record.framed).length ≤ SelectedTranscriptParams.params.D := by
    intro d hd
    exact bound d (List.mem_cons_of_mem c hd)
  have hlen : (c :: tail).length = 25 := by
    have heq := congrArg List.length hrows
    simpa using heq
  have hcount : 1 + tail.length ≤ 25 := by
    simp only [List.length_cons] at hlen
    omega
  have hrow1 : c.after.next_row.val = 1 := by
    have hcarried : c.after.next_row = c.next := by rw [c.carried]
    have hrecordrow := congrArg (fun r : U8 => r.val) c.record_row
    calc
      c.after.next_row.val = c.next.val := congrArg (fun r : U8 => r.val) hcarried
      _ = c.record.row.val + 1 := c.next_row
      _ = c.row.val + 1 := by rw [hrecordrow]
      _ = 1 := by omega
  have hsourceTail : sourceLog tail ⊆ tr := by
    intro q hq
    apply hsourceRows
    rcases List.mem_flatMap.mp hq with ⟨d,hd,hqd⟩
    exact List.mem_flatMap.mpr ⟨d,List.mem_cons_of_mem c hd,hqd⟩
  have htailTrace : SourceFull25.Trace D pre c.after after tail := by
    cases run with
    | cons _ ht => exact ht
  have hpositive := SourceGlobalOracleTrace.positive_trace_simulation htailTrace
    Hbytes tr hsourceTail hcons hboundTail 1 Pnext (by decide) hcount hrow1 hstate
  refine ⟨hboundTail,hempty,?_⟩
  change Pnext.round = 1 ∧ Pnext = sourceInitialPostPrefix P c1 word c ∧
      SourceLiteralTraceLift.literalPrefix Hbytes 1 Pnext tail hboundTail =
        SourceLiteralTraceLift.sourcePrefix 1 Pnext tail hboundTail ∧
      AspisR1.UnifiedSampler.stateOf SelectedTranscriptParams.params
        (LiteralTranscript.erasePrefix
          (SourceLiteralTraceLift.sourcePrefix 1 Pnext tail hboundTail)) =
        decodeState after.state
  have hlenP : P.rounds.length = 0 := by
    simpa [FS.Prefix.round] using hPround
  have hroundNext : Pnext.round = 1 := by
    simp [Pnext,initialPostPrefix,FS.Prefix.round,FS.Prefix.ext,hlenP]
  exact ⟨hroundNext,hpost,hpositive.1,hpositive.2⟩

#print axioms full25_initial_and_positive_prefix
end AspisR1PublicPreparation.SourceGlobalOracleFull25
end
