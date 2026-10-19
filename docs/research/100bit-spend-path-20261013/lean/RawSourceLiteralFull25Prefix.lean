import RawSourceLiteralInitialCall
import RawSourceLiteralTraceLift
import R1CanonicalByteAddress

set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.SourceLiteralFull25Prefix

open Aeneas Aeneas.Std Result
open AspisR1
open AspisR1.LiteralTranscript
open AspisR1.SelectedTranscriptParams
open AspisR1.TranscriptView
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.SqueezeOracleBridge
open FS FS2 FS2.Duplex
open AspisR1PublicPreparation.SourceDigestAddresses

def sourceOracleBytes {Hash : Type} {D : aspis_core.Digest32 Hash}
    (hash : Hash) (input : Slice U8) (root : TranscriptStep.Bytes32) (length : U32) :
    Bytes → State := fun bs =>
  if h : bs.length ≤ SelectedTranscriptParams.L then
    SourceDigestOracle.oracle D hash input root length (Addr.ofBytes bs h)
  else 0

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

theorem sourceOracle_eq_of_toBytes {Hash : Type} {L : Nat}
    (D : aspis_core.Digest32 Hash) (hash : Hash) (input : Slice U8)
    (root : TranscriptStep.Bytes32) (length : U32)
    (a b : Addr L) (hab : a.toBytes = b.toBytes) :
    SourceDigestOracle.oracle D hash input root length a =
      SourceDigestOracle.oracle D hash input root length b := by
  unfold SourceDigestOracle.oracle
  rw [hab]

/-- The actual row-zero source call and the remaining 24 calls simulate one
literal prefix, preserving the same source trace throughout. -/
theorem full25_initial_and_positive_prefix
    {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    {before after : r1_wire.SemanticTranscript Hash}
    {rows : List U8} {qs : List aspis_core.field.QM31}
    (bytes : Slice U8)
    (hparse : PrefixAdapter.parseAccepted bytes = ok (.Ok pre))
    (run : BeginCalls.SemanticRun D pre rows before after qs)
    (hrows : rows.map (fun row => row.val) = List.range 25)
    (pubInput : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (oracleInput : Slice U8) (root : TranscriptStep.Bytes32)
    (hpublic : r1_semantic.public_transcript D pubInput before.hash root =
      ok (.Ok before))
    (P : LiteralTranscript.Prefix) (c1 : State) (word : LiteralTranscript.C1Word)
    (hPround : P.round = 0)
    (hpublicBytes : ∀ encoded : alloc.vec.Vec U8,
      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes pubInput =
        ok (.Ok encoded) →
      P.statement.pubBytes = rawBytes (alloc.vec.Vec.deref encoded))
    (horacleInput : ∀ encoded : alloc.vec.Vec U8,
      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes pubInput =
        ok (.Ok encoded) →
      oracleInput = alloc.vec.Vec.deref encoded)
    (hroot : c1 = decodeState root) :
    ∃ (encoded : alloc.vec.Vec U8) (length : U32)
      (tail : List (SourceFull25.Call D pre)) (values : SemanticPrefixCodec.Full)
      (c : SourceFull25.Call D pre),
      ∃ boundTail : ∀ d ∈ tail,
        (rawBytes d.record.framed).length ≤ SelectedTranscriptParams.params.D,
      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes pubInput =
        ok (.Ok encoded) ∧
      oracleInput = alloc.vec.Vec.deref encoded ∧
      SourceFull25.Trace D pre before after (c :: tail) ∧
      SourceFull25.Trace D pre c.after after tail ∧
      (c :: tail).map (fun d => d.row.val) = List.range 25 ∧
      (c :: tail).map SourceFull25.Call.q = qs ∧
      SourceFull25.rawFrames (c :: tail) = PrefixAdapter.completedRecords pre ∧
      SemanticPrefixCodec.decodeFrom 0 (SourceFull25.rawFrames (c :: tail)) =
        some (SemanticPrefixCodec.entriesOf values) ∧
      (∀ d ∈ c :: tail,
        (d.record.framed.val.map ExtractedRecordByteValue.rawByte).length ≤ 901) ∧
      rawBytes c.record.framed = PublicInitFrame.emptyRecord ∧
      let Hbytes := @sourceOracleBytes Hash D before.hash oracleInput root length
      let Pnext := initialPostPrefix Hbytes P c1 word
      Pnext.round = 1 ∧
      Pnext = sourceInitialPostPrefix P c1 word c ∧
      SourceLiteralTraceLift.literalPrefix Hbytes 1 Pnext tail boundTail =
        SourceLiteralTraceLift.sourcePrefix 1 Pnext tail boundTail ∧
      AspisR1.UnifiedSampler.stateOf SelectedTranscriptParams.params
        (LiteralTranscript.erasePrefix
          (SourceLiteralTraceLift.sourcePrefix 1 Pnext tail boundTail)) =
        decodeState after.state := by
  obtain ⟨encoded, length, tail, values, c, henc, hinput,
    htrace, htailTrace, hrows, hqs, hframes, hdecode, hbound, hrow, hempty,
    hsim⟩ :=
    SourceLiteralInitialCall.full25_trace_first_call_and_tail_simulates_literal_initial
      bytes hparse run hrows pubInput oracleInput root hpublic P c1 word
      hpublicBytes horacleInput hroot
  let Hbytes := @sourceOracleBytes Hash D before.hash oracleInput root length
  have horacle : ∀ a : Addr SelectedTranscriptParams.L,
      SourceDigestOracle.oracle D before.hash oracleInput root length a = Hbytes a.toBytes := by
    intro a
    change SourceDigestOracle.oracle D before.hash oracleInput root length a =
      (if h : a.toBytes.length ≤ SelectedTranscriptParams.L then
        SourceDigestOracle.oracle D before.hash oracleInput root length
          (Addr.ofBytes a.toBytes h) else 0)
    rw [dif_pos (AspisR1.CanonicalByteAddress.length_le a)]
    exact (sourceOracle_eq_of_toBytes D before.hash oracleInput root length a
      (Addr.ofBytes a.toBytes (AspisR1.CanonicalByteAddress.length_le a))
      (Addr.toBytes_ofBytes a.toBytes (AspisR1.CanonicalByteAddress.length_le a)).symm)
  have hfun : (fun a : Addr SelectedTranscriptParams.L =>
      SourceDigestOracle.oracle D before.hash oracleInput root length a) =
      (fun a => Hbytes a.toBytes) := funext horacle
  have hsim' := hsim
  rw [hfun] at hsim'
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
    have h := hbound d (List.mem_cons_of_mem c hd)
    have hmap : rawBytes d.record.framed =
        d.record.framed.val.map ExtractedRecordByteValue.rawByte := by
      unfold SourceDigestAddresses.rawBytes
      apply List.map_congr_left
      intro b hb
      apply Fin.ext
      rfl
    rw [hmap]
    norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D] at h ⊢
    omega
  have hhash : c.after.hash = before.hash := by
    have hcHash := (SourceDigestOracle.trace_hashes htrace).2 c (by simp)
    simpa only [c.carried] using hcHash
  have horacleTail : ∀ a : Addr SelectedTranscriptParams.L,
      SourceDigestOracle.oracle D c.after.hash oracleInput root length a = Hbytes a.toBytes := by
    intro a
    rw [hhash]
    exact horacle a
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
  have hpositive := SourceLiteralTraceLift.positive_trace_simulation htailTrace
    c.after.hash rfl oracleInput root length Hbytes horacleTail hboundTail
    1 Pnext (by decide) hcount hrow1 hstate
  refine ⟨encoded, length, tail, values, c, hboundTail,
    henc, hinput, htrace, htailTrace,
    hrows, hqs, hframes, hdecode, hbound, hempty, ?_⟩
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
    simp [Pnext, initialPostPrefix, FS.Prefix.round, FS.Prefix.ext, hlenP]
  exact ⟨hroundNext, hpost, hpositive.1, hpositive.2⟩

#print axioms full25_initial_and_positive_prefix

end AspisR1PublicPreparation.SourceLiteralFull25Prefix
end

#print axioms AspisR1PublicPreparation.SourceLiteralTraceLift.positive_trace_simulation
