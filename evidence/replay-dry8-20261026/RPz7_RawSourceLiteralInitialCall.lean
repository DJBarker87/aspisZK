import RPz7_RawSourceLiteralSamplerStep
import RPz7_RawSourceLiteralTraceLift
import RPz7_ExtractedSourceFull25Typed
import R1LiteralSemanticCodecBridge
import R1LiteralByteSampler
import R1SelectedTranscriptParams

set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.SourceLiteralInitialCall

open Aeneas Aeneas.Std Result
open AspisR1
open AspisR1.TranscriptView
open AspisR1.LiteralTranscript
open AspisR1.SelectedTranscriptParams
open AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.DuplexFrames AspisV8R19.MemoizedProgramLaw
open AspisR1PublicPreparation.SourceDigestAddresses
open AspisV8R15.ExactTowerBase
open FS FS2 FS2.Duplex

private abbrev params :=
  SelectedTranscriptParams.params

private abbrev sourceChallenge {Hash : Type} {D : aspis_core.Digest32 Hash}
    {pre : r1_wire.Prefix} (c : SourceFull25.Call D pre) : AspisWideTower.WideExact :=
  algebraMap QM31Exact AspisWideTower.WideExact
    (ExtractedCurrentQM31Exact.decode
      (ExtractedQM31SamplerCarrier.toCurrent (SamplerTransport.toOld c.q)))

/-- The actual row-zero source call agrees with the literal public initializer.
The two explicit bridge facts are the real first-call inputs: its prior state
is the digest of the public initializer address, and its validated framed row
is the canonical empty record. The source trace supplies all later digest
outputs through the functional oracle theorem. -/
theorem call_simulates_literal_initial
    {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    {before after : r1_wire.SemanticTranscript Hash}
    {cs : List (SourceFull25.Call D pre)}
    (run : SourceFull25.Trace D pre before after cs)
    (c : SourceFull25.Call D pre) (hc : c ∈ cs)
    (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32)
    (H : Addr SelectedTranscriptParams.L → State)
    (horacle : ∀ a : Addr SelectedTranscriptParams.L,
      SourceDigestOracle.oracle D before.hash pubInput root length a = H a)
    (hD : ∀ d ∈ cs, (rawBytes d.record.framed).length ≤ params.D)
    (hrow : c.row.val = 0)
    (P : LiteralTranscript.Prefix) (c1 : State) (word : LiteralTranscript.C1Word)
    (hinit : decodeState c.before.state = H (PublicInitFrame.addr P.statement.pubBytes P.statement.initFits c1))
    (hempty : rawBytes c.record.framed = PublicInitFrame.emptyRecord) :
    Value.ordinary (sourceChallenge c) =
      (eval H
        (LiteralTranscript.samp 0 P (.initial c1 word)).toProgram).2.1 ∧
    decodeState c.after.state =
      (eval H
        (LiteralTranscript.samp 0 P (.initial c1 word)).toProgram).2.2 := by
  have hbound : (rawBytes c.record.framed).length ≤ params.D := hD c hc
  have htagcode : c.tag.val = 160 := by
    have ht := c.tag_code
    rw [c.record_row, hrow] at ht
    simpa using ht
  have htag : decodeByte c.tag = 160 := by
    apply Fin.ext
    exact htagcode
  have h5 : 5 ≤ params.D := by
    norm_num [SelectedTranscriptParams.params, SelectedTranscriptParams.D, params]
  let initAddr := PublicInitFrame.addr P.statement.pubBytes P.statement.initFits c1
  let initState := H initAddr
  let rowAddr := PublicInitFrame.row0 params h5 initState
  let rowState := H rowAddr
  change decodeState c.before.state = initState at hinit
  have habsorb : absorbA params (decodeState c.before.state) (decodeByte c.tag)
      (rawBytes c.record.framed) hbound = rowAddr := by
    apply Subtype.ext
    simp [rowAddr, PublicInitFrame.row0, absorbA, initState, hinit, htag, hempty]
  have htrace := SourceDigestOracle.trace_functional params
    run pubInput root length hD c hc
  have habsVal : decodeState c.absorbed = rowState := by
    calc
      decodeState c.absorbed = SourceDigestOracle.oracle D before.hash pubInput root length
          (absorbA params (decodeState c.before.state) (decodeByte c.tag)
            (rawBytes c.record.framed) hbound) := htrace.1
      _ = H rowAddr := by rw [horacle, habsorb]
      _ = rowState := rfl
  have hblock : decodeState c.block = H (squeezeA params rowState) := by
    calc
      decodeState c.block = SourceDigestOracle.oracle D before.hash pubInput root length
          (squeezeA params (decodeState c.absorbed)) := htrace.2.1
      _ = H (squeezeA params (decodeState c.absorbed)) := horacle _
      _ = H (squeezeA params rowState) := by rw [habsVal]
  have hnext : decodeState c.after.state = H (advanceA params rowState) := by
    calc
      decodeState c.after.state = SourceDigestOracle.oracle D before.hash pubInput root length
          (advanceA params (decodeState c.absorbed)) := htrace.2.2
      _ = H (advanceA params (decodeState c.absorbed)) := horacle _
      _ = H (advanceA params rowState) := by rw [habsVal]
  have hq := AspisR1PublicPreparation.SourceSemanticSampler.call_semChal c
  have hchallenge : sourceChallenge c = params.σ 0 (H (squeezeA params rowState)) := by
    calc
      sourceChallenge c = R0P.SemSource.semChal (decodeState c.block) := hq
      _ = params.σ 0 (H (squeezeA params rowState)) := by
        rw [SelectedTranscriptParams.params_sigma,
          SelectedChallengeMap.semantic_row 0 (by omega)]
        rw [hblock]
  have hliteral :
      eval H (LiteralTranscript.samp 0 P (.initial c1 word)).toProgram =
        ([(initAddr, H initAddr), (rowAddr, rowState),
          (squeezeA params rowState, H (squeezeA params rowState)),
          (advanceA params rowState, H (advanceA params rowState))],
          TranscriptView.liftChallenge
            (params.σ 0 (H (squeezeA params rowState)), H (advanceA params rowState))) := by
    change eval H
      (UnifiedSampler.samp params h5 0 (LiteralTranscript.erasePrefix P) (.initial c1)).toProgram = _
    rw [UnifiedSampler.row_zero]
    rw [AspisR1.DuplexSamplers.initial_eval]
    rfl
  rw [hliteral]
  constructor
  · change Value.ordinary (sourceChallenge c) =
      Value.ordinary (params.σ 0 (H (squeezeA params rowState)))
    exact congrArg Value.ordinary hchallenge
  · change decodeState c.after.state = H (advanceA params rowState)
    exact hnext

#print axioms call_simulates_literal_initial
#print axioms AspisR1PublicPreparation.SourceLiteralTraceLift.positive_trace_simulation

/-- The actual successful full25 typed decode forces the first source frame to
the canonical empty row-zero payload. This is the source-call frame, via the
exact `rawFrames` projection, rather than a separately chosen literal row. -/
theorem first_framed_empty
    {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (c : SourceFull25.Call D pre) (tail : List (SourceFull25.Call D pre))
    (values : SemanticPrefixCodec.Full)
    (hdecode : SemanticPrefixCodec.decodeFrom 0
      (SourceFull25.rawFrames (c :: tail)) =
        some (SemanticPrefixCodec.entriesOf values)) :
    rawBytes c.record.framed = PublicInitFrame.emptyRecord := by
  let raw := rawBytes c.record.framed
  have hraw : raw = c.record.framed.val.map ExtractedRecordByteValue.rawByte := by
    unfold raw SourceDigestAddresses.rawBytes
    apply List.map_congr_left
    intro b hb
    apply Fin.ext
    rfl
  have hframes : SourceFull25.rawFrames (c :: tail) =
      raw :: SourceFull25.rawFrames tail := by
    simp [SourceFull25.rawFrames, hraw]
  have hdecode' : SemanticPrefixCodec.decodeFrom 0
      (raw :: SourceFull25.rawFrames tail) =
        some (SemanticPrefixCodec.entriesOf values) := by
    rw [← hframes]
    exact hdecode
  have hfirst : SemanticPrefixCodec.decodeOne 0 raw ≠ none := by
    intro hnone
    simp [SemanticPrefixCodec.decodeFrom, TypedPrefixParser.decode, hnone] at hdecode'
  cases hrowdecode : SemanticRecordCodec.decode 0 raw with
  | none =>
      have hnone : SemanticPrefixCodec.decodeOne 0 raw = none := by
        simp [SemanticPrefixCodec.decodeOne, hrowdecode]
      exact (hfirst hnone).elim
  | some payload =>
      exact LiteralSemanticCodecBridge.row_zero_record_of_decode raw payload hrowdecode

/-- The typed full-25 run exposes the actual first source call. Its typed
prefix decoding fixes the empty row-zero frame, and a successful source public
initializer fixes the call's prior state. The two explicit correspondences
are only representation links: parsed public bytes to the literal statement,
and the source root bytes to the literal root state. -/
theorem full25_trace_first_call_and_tail_simulates_literal_initial
    {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (bytes : Slice U8)
    (hparse : PrefixAdapter.parseAccepted bytes = ok (.Ok pre))
    {rows : List U8} {before after : r1_wire.SemanticTranscript Hash}
    {qs : List aspis_core.field.QM31}
    (run : BeginCalls.SemanticRun D pre rows before after qs)
    (hrows : rows.map (fun row => row.val) = List.range 25)
    (pubInput : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (oracleInput : Slice U8)
    (root : TranscriptStep.Bytes32)
    (hpublic : r1_semantic.public_transcript D pubInput before.hash root =
      ok (.Ok before))
    (P : LiteralTranscript.Prefix) (c1 : State) (word : LiteralTranscript.C1Word)
    (hpublicBytes : ∀ encoded : alloc.vec.Vec U8,
      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes pubInput =
        ok (.Ok encoded) →
      P.statement.pubBytes = rawBytes (alloc.vec.Vec.deref encoded))
    (horacleInput : ∀ encoded : alloc.vec.Vec U8,
      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes pubInput =
        ok (.Ok encoded) →
      oracleInput = alloc.vec.Vec.deref encoded)
    (hroot : c1 = decodeState root)
    :
    ∃ (encoded : alloc.vec.Vec U8) (length : U32)
      (tail : List (SourceFull25.Call D pre)) (values : SemanticPrefixCodec.Full)
      (c : SourceFull25.Call D pre),
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
      (∀ d ∈ c :: tail, (d.record.framed.val.map ExtractedRecordByteValue.rawByte).length ≤ 901) ∧
      c.row.val = 0 ∧
      rawBytes c.record.framed = PublicInitFrame.emptyRecord ∧
      (Value.ordinary (sourceChallenge c) =
        (eval (fun a : Addr SelectedTranscriptParams.L =>
          SourceDigestOracle.oracle D before.hash oracleInput root length a)
          (LiteralTranscript.samp 0 P (.initial c1 word)).toProgram).2.1 ∧
       decodeState c.after.state =
        (eval (fun a : Addr SelectedTranscriptParams.L =>
          SourceDigestOracle.oracle D before.hash oracleInput root length a)
          (LiteralTranscript.samp 0 P (.initial c1 word)).toProgram).2.2) := by
  obtain ⟨cs, values, htrace, hcallrows, hcallqs, hframes, hdecode, hbound⟩ :=
    SourceFull25.run_typedFull D bytes pre hparse run hrows
  have hrows' : cs.map (fun d => d.row.val) = List.range 25 := by
    have hm := congrArg (List.map (fun u : U8 => u.val)) hcallrows
    simpa only [List.map_map, Function.comp_def] using hm.trans hrows
  cases hcs : cs with
  | nil =>
      rw [hcs] at hrows'
      simp at hrows'
  | cons c tail =>
      rw [hcs] at hrows' hcallrows hcallqs hframes hdecode hbound htrace
      have hrow : c.row.val = 0 := by
        have hh := congrArg (fun xs : List Nat => xs[0]?) hrows'
        simpa using hh
      have hempty := first_framed_empty c tail values hdecode
      have hc : c ∈ c :: tail := by simp
      have hD : ∀ d ∈ c :: tail, (rawBytes d.record.framed).length ≤ params.D := by
        intro d hd
        have hb := hbound d hd
        have hmap : rawBytes d.record.framed =
            d.record.framed.val.map ExtractedRecordByteValue.rawByte := by
          unfold SourceDigestAddresses.rawBytes
          apply List.map_congr_left
          intro b hb'
          apply Fin.ext
          rfl
        rw [hmap]
        norm_num [params, SelectedTranscriptParams.params, SelectedTranscriptParams.D] at hb ⊢
        omega
      have hcbefore : c.before = before := by
        cases htrace
        rfl
      obtain ⟨encoded, length, henc, hhash, hpublicOracle⟩ :=
        SourceDigestOracle.public_oracle D before.hash pubInput root before hpublic
      have hinput := horacleInput encoded henc
      have hpubbytes := hpublicBytes encoded henc
      have hL : 75 + (rawBytes (alloc.vec.Vec.deref encoded)).length ≤
          SelectedTranscriptParams.L := by
        rw [← hpubbytes]
        exact P.statement.initFits
      have hinitSource := hpublicOracle hL
      have hsourceAddress :
          PublicInitFrame.addr (rawBytes (alloc.vec.Vec.deref encoded)) hL
            (decodeState root) =
          PublicInitFrame.addr P.statement.pubBytes P.statement.initFits c1 := by
        unfold PublicInitFrame.addr FS2.Duplex.Addr.ofBytes
        apply Subtype.ext
        simp [PublicInitFrame.frame, TrailingStateFrame.frame,
          PublicInitFrame.pre, hpubbytes, hroot]
      have hinit : decodeState c.before.state =
          SourceDigestOracle.oracle D before.hash oracleInput root length
            (PublicInitFrame.addr P.statement.pubBytes P.statement.initFits c1) := by
        rw [hcbefore]
        calc
          decodeState before.state =
              SourceDigestOracle.oracle D before.hash (alloc.vec.Vec.deref encoded) root length
                (PublicInitFrame.addr (rawBytes (alloc.vec.Vec.deref encoded)) hL
                  (decodeState root)) := hinitSource
          _ = SourceDigestOracle.oracle D before.hash (alloc.vec.Vec.deref encoded) root length
                (PublicInitFrame.addr P.statement.pubBytes P.statement.initFits c1) := by
                  exact congrArg (fun a => SourceDigestOracle.oracle D before.hash
                    (alloc.vec.Vec.deref encoded) root length a) hsourceAddress
          _ = SourceDigestOracle.oracle D before.hash oracleInput root length
                (PublicInitFrame.addr P.statement.pubBytes P.statement.initFits c1) := by
                  rw [hinput]
      let H : Addr SelectedTranscriptParams.L → State := fun a =>
        SourceDigestOracle.oracle D before.hash oracleInput root length a
      have hsim := call_simulates_literal_initial htrace c hc oracleInput root length H
        (by intro a; rfl) hD hrow P c1 word hinit hempty
      have hrowsRange : (c :: tail).map (fun d => d.row.val) = List.range 25 := by
        have hm := congrArg (List.map (fun row : U8 => row.val)) hcallrows
        simpa only [List.map_map, Function.comp_def] using hm.trans hrows
      have hq' : (c :: tail).map SourceFull25.Call.q = qs := hcallqs
      have htailTrace : SourceFull25.Trace D pre c.after after tail := by
        cases htrace with
        | cons _ ht => exact ht
      exact ⟨encoded, length, tail, values, c, henc, hinput,
        htrace, htailTrace, hrowsRange, hq', hframes, hdecode, hbound, hrow, hempty, hsim⟩

#print axioms first_framed_empty
#print axioms full25_trace_first_call_and_tail_simulates_literal_initial
end AspisR1PublicPreparation.SourceLiteralInitialCall
end
