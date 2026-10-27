import RPz7_RawSourceGlobalOracleCoupling
import R1LiteralByteSampler

/-! The actual public initializer and row zero under the same globally logged
byte oracle, without constructing a separate all-address source oracle. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.SourceGlobalOracleInitial
open Aeneas Aeneas.Std Result
open AspisR1 AspisR1.TranscriptView
open AspisR1.LiteralTranscript AspisR1.SelectedTranscriptParams
open AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.DuplexFrames AspisV8R19.MemoizedProgramLaw
open AspisR1PublicPreparation.SourceDigestAddresses
open AspisV8R15.ExactTowerBase
open FS FS2 FS2.Duplex
open SourceDigestLog
private abbrev params := SelectedTranscriptParams.params
abbrev sourceChallenge := @SourceLiteralTraceLift.sourceChallenge

/-- The exact successful public serializer/constructor digest call. -/
structure PublicInitCall {Hash : Type} (D : aspis_core.Digest32 Hash)
    (pubInput : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (root : TranscriptStep.Bytes32) (before : r1_wire.SemanticTranscript Hash) where
  encoded : alloc.vec.Vec U8
  length : U32
  state : TranscriptStep.Bytes32
  serialized : pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes pubInput =
    ok (.Ok encoded)
  converted : core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from
    (Slice.len (alloc.vec.Vec.deref encoded)) = ok (.Ok length)
  digest : D.digest before.hash (TranscriptStep.initParts (alloc.vec.Vec.deref encoded) root length) =
    ok state
  carried : before = { state, hash := before.hash, next_row := 0#u8 }

theorem public_success_has_init_call
    {Hash : Type} (D : aspis_core.Digest32 Hash)
    (pubInput : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (root : TranscriptStep.Bytes32) (before : r1_wire.SemanticTranscript Hash)
    (hpublic : r1_semantic.public_transcript D pubInput before.hash root = ok (.Ok before)) :
    Nonempty (PublicInitCall D pubInput root before) := by
  obtain ⟨encoded,hencoded,hnew⟩ := public_new D before.hash pubInput root before hpublic
  obtain ⟨length,state,hlen,hdigest,hcarried⟩ :=
    TranscriptStep.new_success D before.hash (alloc.vec.Vec.deref encoded) root before hnew
  exact ⟨⟨encoded,length,state,hencoded,hlen,hdigest,hcarried⟩⟩

def initPair {Hash : Type} {D : aspis_core.Digest32 Hash}
    {pubInput : pool_v1.pair_forest_semantic_terminal.r0.Public}
    {root : TranscriptStep.Bytes32} {before : r1_wire.SemanticTranscript Hash}
    (c : PublicInitCall D pubInput root before) : Bytes × State :=
  (flatten (TranscriptStep.initParts (alloc.vec.Vec.deref c.encoded) root c.length),decodeState c.state)

/-- The actual initialized state is the global oracle value at the literal
statement's public-initializer address. Log membership and the two public/root
representation equalities are the remaining source interfaces. -/
theorem initializer_state_from_log
    {Hash : Type} {D : aspis_core.Digest32 Hash}
    {pubInput : pool_v1.pair_forest_semantic_terminal.r0.Public}
    {root : TranscriptStep.Bytes32} {before : r1_wire.SemanticTranscript Hash}
    (c : PublicInitCall D pubInput root before)
    (Hbytes : Bytes → State) (tr : List (Bytes × State))
    (hinitLog : initPair c ∈ tr) (hcons : ∀ q ∈ tr, q.2 = Hbytes q.1)
    (P : LiteralTranscript.Prefix) (c1 : State)
    (hpublicBytes : P.statement.pubBytes = rawBytes (alloc.vec.Vec.deref c.encoded))
    (hroot : c1 = decodeState root) :
    decodeState before.state = Hbytes
      (PublicInitFrame.addr P.statement.pubBytes P.statement.initFits c1).toBytes := by
  have hL : 75 + (rawBytes (alloc.vec.Vec.deref c.encoded)).length ≤ SelectedTranscriptParams.L := by
    rw [← hpublicBytes]
    exact P.statement.initFits
  have haddr := init_address (alloc.vec.Vec.deref c.encoded) root c.length
    (successful_length _ _ c.converted) hL
  have hsame : PublicInitFrame.addr (rawBytes (alloc.vec.Vec.deref c.encoded)) hL
      (decodeState root) = PublicInitFrame.addr P.statement.pubBytes P.statement.initFits c1 := by
    unfold PublicInitFrame.addr FS2.Duplex.Addr.ofBytes
    apply Subtype.ext
    simp [PublicInitFrame.frame,TrailingStateFrame.frame,PublicInitFrame.pre,hpublicBytes,hroot]
  have hvalue := hcons _ hinitLog
  change decodeState c.state = Hbytes (flatten _) at hvalue
  rw [haddr,hsame] at hvalue
  have hstate : before.state = c.state := congrArg (fun t => t.state) c.carried
  rw [hstate]
  exact hvalue

/-- Reached row-zero source success agrees with the literal initializer under
one globally logged oracle; no equality on unqueried addresses is supplied. -/
theorem call_simulates_literal_initial
    {Hash : Type} {D : aspis_core.Digest32 Hash} {pre : r1_wire.Prefix}
    (cs : List (SourceFull25.Call D pre)) (c : SourceFull25.Call D pre) (hc : c ∈ cs)
    (Hbytes : Bytes → State) (tr : List (Bytes × State))
    (hsource : sourceLog cs ⊆ tr) (hcons : ∀ q ∈ tr, q.2 = Hbytes q.1)
    (hD : ∀ d ∈ cs, (rawBytes d.record.framed).length ≤ params.D)
    (hrow : c.row.val = 0)
    (P : LiteralTranscript.Prefix) (c1 : State) (word : LiteralTranscript.C1Word)
    (hinit : decodeState c.before.state = Hbytes
      (PublicInitFrame.addr P.statement.pubBytes P.statement.initFits c1).toBytes)
    (hempty : rawBytes c.record.framed = PublicInitFrame.emptyRecord) :
    Value.ordinary (sourceChallenge c) =
      (eval (fun a : Addr SelectedTranscriptParams.L => Hbytes a.toBytes)
        (LiteralTranscript.samp 0 P (.initial c1 word)).toProgram).2.1 ∧
    decodeState c.after.state =
      (eval (fun a : Addr SelectedTranscriptParams.L => Hbytes a.toBytes)
        (LiteralTranscript.samp 0 P (.initial c1 word)).toProgram).2.2 := by
  let H : Addr SelectedTranscriptParams.L → State := fun a => Hbytes a.toBytes
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
  have htrace := SourceGlobalOracleCoupling.call_functional_from_log params cs c hc
    Hbytes tr hsource hcons hbound
  have habsVal : decodeState c.absorbed = rowState := by
    change decodeState c.absorbed = Hbytes rowAddr.toBytes
    rw [← habsorb]
    exact htrace.1
  have hblock : decodeState c.block = H (squeezeA params rowState) := by
    change decodeState c.block = Hbytes (squeezeA params rowState).toBytes
    rw [← habsVal]
    exact htrace.2.1
  have hnext : decodeState c.after.state = H (advanceA params rowState) := by
    change decodeState c.after.state = Hbytes (advanceA params rowState).toBytes
    rw [← habsVal]
    exact htrace.2.2
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

#print axioms public_success_has_init_call
#print axioms initializer_state_from_log
#print axioms call_simulates_literal_initial
end AspisR1PublicPreparation.SourceGlobalOracleInitial
end
