import ExtractedSourceCanonicalRecovery
import ExtractedCircleCalls
import ExtractedSourceCircleFrameBound
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.SourceFirstTyped
open r1_wire BeginCalls AspisR1
open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

/-- One paired caller witness supplies the same public constructor, source25
log and actual next absorb. No independent child-success/bytes/target premise. -/
theorem first_inputs {E : Type} (invalidAccountData : E)
    (T : Tx1Model.Boundaries) (P : PreparedModel.Boundaries)
    (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    (D : aspis_core.Digest32 Unit)
    (mark : FirstCaller.Phase → Result Unit) (error : verifier.Error → Result E)
    (asf8 proof : Slice U8) (k : Usize) (out : alloc.vec.Vec U8)
    (h : FirstCaller.first invalidAccountData
      (FirstHelperBinding.tx1 T P (FinishModel.finish R B) D) mark error asf8 proof k =
        ok (.Ok out)) :
    ∃ (sem : r1_semantic.Verified Unit) (pre : Prefix)
      (initial t25 : SemanticTranscript Unit),
      ∃ cs : List (SourceFull25.Call D pre),
      ∃ bound : ∀ c ∈ cs,
        (c.record.framed.val.map ExtractedRecordByteValue.rawByte).length ≤ 901,
      ∃ (values : SemanticPrefixCodec.Full) (bytes : alloc.vec.Vec U8)
        (wire : SemanticPublicWire.Wire) (record25 : ValidatedRecord)
        (targetTag : U8) (targetOutput : TranscriptStep.Bytes32),
        SourceFull25.Trace D pre initial t25 cs ∧
        cs.map SourceFull25.Call.row = ActualFull25.rows ∧
        cs.map SourceFull25.Call.q = challengeList sem.challenges ++ sem.alpha.val ∧
        SourceFull25.rawFrames cs = PrefixAdapter.completedRecords pre ∧
        SemanticPrefixCodec.decodeFrom 0 (SourceFull25.rawFrames cs) =
          some (SemanticPrefixCodec.entriesOf values) ∧
        SemanticPublicWire.parsePublic
          (bytes.val.map AspisR1PublicSerializer.RawBridge431.rawByte) =
            some (SemanticPublicWire.toPublic wire) ∧
        SemanticTranscript.new D () (alloc.vec.Vec.deref bytes) pre.c1_root = ok (.Ok initial) ∧
        (75 + (SourceDigestAddresses.rawBytes (alloc.vec.Vec.deref bytes)).length ≤
          SelectedTranscriptParams.L) ∧
        ((SourceDigestAddresses.rawBytes (alloc.vec.Vec.deref bytes)).length < 2^32) ∧
        sem.state_before_z0 = t25.state ∧
        Prefix.validated_record pre 25#u8 = ok (.Ok record25) ∧
        targetTag.val = 185 ∧
        (SourceDigestAddresses.rawBytes record25.framed).length ≤ SelectedTranscriptParams.params.D ∧
        D.digest t25.hash (TranscriptStep.absorbParts t25.state targetTag record25.framed) =
          ok targetOutput := by
  obtain ⟨s,supplied,view,sem,prepared,pre,initial,afterBegin,challenges,
    hd,heq,hview,hparse,hpublic,hbegin,hfinish,hprepare⟩ :=
    FirstPaired.first_paired invalidAccountData T P R B D mark error asf8 proof k out h
  obtain ⟨running,t25,r25,r26,z0,t26,z1,t27,
    hrounds,hch,hstate,htranscript,hclaims,hr25,hd25,hz0,hr26,hd26,hz1,hz⟩ :=
    FinishCalls.finish_success R B D supplied pre afterBegin challenges
      (some (fun phase => mark (FirstHelperBinding.phaseToFirst phase))) sem hfinish
  obtain ⟨qb,hb,eqb⟩ := begin_success D pre initial afterBegin challenges hbegin
  obtain ⟨qr,hr,eqr⟩ := RoundCalls.rounds_success R D pre afterBegin t25 running sem.alpha hrounds
  have run : SemanticRun D pre ActualFull25.rows initial t25
      (challengeList sem.challenges ++ sem.alpha.val) := by
    rw [hch,← eqb,← eqr]
    exact ActualFull25.append_run D pre hb hr
  obtain ⟨cs,values,trace,hrows,hqs,hbytes,hdecode,bound⟩ :=
    SourceFull25.run_typedFull D view.semantic pre hparse run ActualFull25.rows_schedule
  have hpublic' : r1_semantic.public_transcript D (PreparationBinding.preparationPublic s) ()
      pre.c1_root = ok (.Ok initial) := heq ▸ hpublic
  obtain ⟨bytes,wire,hs,hw,hpubParse,hnew⟩ :=
    PreparationBinding.decoder_helper_parsePublic D asf8 s () pre.c1_root initial hd hpublic'
  have hfit := SemanticPublicCodecComplete.parsed_init_fits _ _ hpubParse
  have hsmall : 75 + (SourceDigestAddresses.rawBytes (alloc.vec.Vec.deref bytes)).length ≤ 1530 := by
    simpa only [SourceDigestAddresses.rawBytes, alloc.vec.Vec.deref, List.length_map] using hfit
  have hL : 75 + (SourceDigestAddresses.rawBytes (alloc.vec.Vec.deref bytes)).length ≤
      SelectedTranscriptParams.L := by
    dsimp only [SelectedTranscriptParams.L]
    omega
  have hpub : (SourceDigestAddresses.rawBytes (alloc.vec.Vec.deref bytes)).length < 2^32 := by
    have hp := SemanticPublicCodecComplete.parsed_length_u32 _ _ hpubParse
    simpa only [SourceDigestAddresses.rawBytes, alloc.vec.Vec.deref, List.length_map] using hp
  have hrow25 : r25.row = 25#u8 :=
    (SourceFull25.validated_record_bytes pre 25#u8 r25 hr25).1
  obtain ⟨hnext,block,tag,next,absorbed,state,htag,hn,ha,h1,h2,hpoint,hcarry⟩ :=
    CircleCalls.circle25_step B D t25 t26 r25 z0 hrow25 hz0
  have hlen25 := SourceCircleFrameBound.row25_length view.semantic pre r25 hparse hr25
  have hbound25 : (SourceDigestAddresses.rawBytes r25.framed).length ≤
      SelectedTranscriptParams.params.D := by
    change (SourceDigestAddresses.rawBytes r25.framed).length ≤ 3717
    simpa only [SourceDigestAddresses.rawBytes, List.length_map, hlen25] using (Nat.le_refl 3717)
  exact ⟨sem,pre,initial,t25,cs,bound,values,bytes,wire,r25,tag,absorbed,
    trace,hrows,hqs,hbytes,hdecode,hpubParse,hnew,hL,hpub,hstate,hr25,htag,hbound25,ha⟩

/-- The same source records complete to the same returned challenges on any
H-consistent table. This can be instantiated at the typed recovery target. -/
def Reading
    (recoverC2 : State → SemanticPayloadView.InitialWord × SemanticPayloadView.InitialWord)
    (sem : r1_semantic.Verified Unit) (values : SemanticPrefixCodec.Full)
    (table : Table (Addr SelectedTranscriptParams.L) State)
    (H : Addr SelectedTranscriptParams.L → State)
    (rs : List (Rec SelectedTranscriptParams.Message)) : Prop :=
  SelectedSemanticPrefix.read recoverC2 0 (SelectedCompletedSemantic.pairs table H 0 rs) =
    some (((SemanticPrefixCodec.entriesOf values).map
      (fun e => SemanticPayloadView.toMessage recoverC2 e.2.value.val)).zip
        ((BeginCalls.challengeList sem.challenges ++ sem.alpha.val).map SelectedSourceAgreement.sourceChallenge)) ∧
  R0P.Mask.semChalsZ (SelectedSemanticPrefixFacts.lift
    (((SemanticPrefixCodec.entriesOf values).map
      (fun e => SemanticPayloadView.toMessage recoverC2 e.2.value.val)).zip
        ((BeginCalls.challengeList sem.challenges ++ sem.alpha.val).map SelectedSourceAgreement.sourceChallenge))) =
    some ((BeginCalls.challengeList sem.challenges ++ sem.alpha.val).map SelectedSourceAgreement.sourceChallenge)

theorem completed_read (D : aspis_core.Digest32 Unit) (pre : r1_wire.Prefix)
    (initial last : r1_wire.SemanticTranscript Unit)
    (cs : List (SourceFull25.Call D pre)) (run : SourceFull25.Trace D pre initial last cs)
    (hr : cs.map SourceFull25.Call.row = ActualFull25.rows)
    (bound : ∀ c ∈ cs, (c.record.framed.val.map ExtractedRecordByteValue.rawByte).length ≤ 901)
    (sem : r1_semantic.Verified Unit)
    (hq : cs.map SourceFull25.Call.q = BeginCalls.challengeList sem.challenges ++ sem.alpha.val)
    (values : SemanticPrefixCodec.Full)
    (hdecode : SemanticPrefixCodec.decodeFrom 0 (SourceFull25.rawFrames cs) =
      some (SemanticPrefixCodec.entriesOf values))
    (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32)
    (hhash : initial.hash = ())
    (recoverC2 : State → SemanticPayloadView.InitialWord × SemanticPayloadView.InitialWord)
    (table : Table (Addr SelectedTranscriptParams.L) State)
    (htable : ∀ a v, table a = some v →
      v = SourceDigestOracle.oracle D () pubInput root length a) :
    Reading recoverC2 sem values table (SourceDigestOracle.oracle D () pubInput root length)
      (SelectedSourceRecords.records cs bound) := by
  have hqs := SelectedSourceAgreement.source_completed_qs cs run hr bound pubInput root length table
    (by simpa only [hhash] using htable)
  rw [hhash] at hqs
  have hactual : cs.map (fun c => SelectedSourceAgreement.sourceChallenge c.q) =
      (BeginCalls.challengeList sem.challenges ++ sem.alpha.val).map SelectedSourceAgreement.sourceChallenge := by
    simpa only [List.map_map,Function.comp_def] using congrArg (List.map SelectedSourceAgreement.sourceChallenge) hq
  have hqfinal := hqs.trans hactual
  have hd : SemanticPrefixCodec.decodeFrom 0
      ((SelectedSourceRecords.records cs bound).map (fun r => r.2.2.1.val)) =
      some (SemanticPrefixCodec.entriesOf values) := by
    rw [SelectedSourceRecords.records_bytes]; exact hdecode
  have hread := SemanticPrefixCompletedAgreement.completed_read_of_decode recoverC2 table
    (SourceDigestOracle.oracle D () pubInput root length) 0 (SelectedSourceRecords.records cs bound)
    (SemanticPrefixCodec.entriesOf values) hd
  rw [hqfinal] at hread
  refine ⟨hread,?_⟩
  simpa only [hqfinal] using SelectedCompletedSemantic.semChalsZ_read recoverC2 0 table
    (SourceDigestOracle.oracle D () pubInput root length) (SelectedSourceRecords.records cs bound) _ hread


theorem semantic_frame_bound {D : aspis_core.Digest32 Unit} {pre : Prefix}
    (c : SourceFull25.Call D pre)
    (h : (c.record.framed.val.map ExtractedRecordByteValue.rawByte).length ≤ 901) :
    (SourceDigestAddresses.rawBytes c.record.framed).length ≤ SelectedTranscriptParams.params.D := by
  change (SourceDigestAddresses.rawBytes c.record.framed).length ≤ 3717
  simp only [SourceDigestAddresses.rawBytes,List.length_map] at *
  omega

/-- Actual first acceptance gives the SAME strict parsed records, target,
source-derived oracle and table for typed recovery, already-read membership
and the exact source challenge read. The no-hit and whole-trace conditions
are explicit; literal auxiliary-word custody is not asserted. -/
theorem first_typed {E : Type} (invalidAccountData : E)
    (T : Tx1Model.Boundaries) (P : PreparedModel.Boundaries)
    (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    (D : aspis_core.Digest32 Unit)
    (mark : FirstCaller.Phase → Result Unit) (error : verifier.Error → Result E)
    (asf8 proof : Slice U8) (k : Usize) (out : alloc.vec.Vec U8)
    (h : FirstCaller.first invalidAccountData
      (FirstHelperBinding.tx1 T P (FinishModel.finish R B) D) mark error asf8 proof k = ok (.Ok out)) :
    ∃ (sem : r1_semantic.Verified Unit) (pre : Prefix) (initial t25 : SemanticTranscript Unit),
    ∃ (cs : List (SourceFull25.Call D pre))
      (bound : ∀ c ∈ cs, (c.record.framed.val.map ExtractedRecordByteValue.rawByte).length ≤ 901)
      (values : SemanticPrefixCodec.Full) (publicBytes : alloc.vec.Vec U8)
      (record25 : ValidatedRecord) (tag : U8) (output : TranscriptStep.Bytes32),
      SourceFull25.Trace D pre initial t25 cs ∧
      cs.map SourceFull25.Call.row = ActualFull25.rows ∧
      cs.map SourceFull25.Call.q = challengeList sem.challenges ++ sem.alpha.val ∧
      SourceFull25.rawFrames cs = PrefixAdapter.completedRecords pre ∧
      SemanticPrefixCodec.decodeFrom 0 (SourceFull25.rawFrames cs) =
        some (SemanticPrefixCodec.entriesOf values) ∧
      sem.state_before_z0 = t25.state ∧
      Prefix.validated_record pre 25#u8 = ok (.Ok record25) ∧ tag.val = 185 ∧
      D.digest t25.hash (TranscriptStep.absorbParts t25.state tag record25.framed) = ok output ∧
      ∃ (hL : 75 + (SourceDigestAddresses.rawBytes (alloc.vec.Vec.deref publicBytes)).length ≤ SelectedTranscriptParams.L)
        (targetBound : (SourceDigestAddresses.rawBytes record25.framed).length ≤ SelectedTranscriptParams.params.D)
        (length : U32) (target : Addr SelectedTranscriptParams.L)
        (tr : List (Addr SelectedTranscriptParams.L × State)),
      let H := SourceDigestOracle.oracle D () (alloc.vec.Vec.deref publicBytes) pre.c1_root length
      target = absorbA SelectedTranscriptParams.params (decodeState t25.state) (decodeByte tag)
        (SourceDigestAddresses.rawBytes record25.framed) targetBound ∧
      tr = SourceObservations.relevant SelectedTranscriptParams.params cs
        (fun c hc => semantic_frame_bound c (bound c hc))
        (PublicInitFrame.addr (SourceDigestAddresses.rawBytes (alloc.vec.Vec.deref publicBytes)) hL
          (decodeState pre.c1_root),decodeState initial.state) (target,decodeState output) ∧
      tr.length = 77 ∧ (∀ q ∈ tr, q.2 = H q.1) ∧ Read tr target ∧
      ((¬ hitsBad (badColl SelectedTranscriptParams.params 77) emptyTable tr) →
        UnifiedSemanticRecovery.typed SelectedTranscriptParams.params
          (SourceDigestAddresses.rawBytes (alloc.vec.Vec.deref publicBytes))
          (tableBefore emptyTable tr target) 25 (decodeState t25.state) =
            some (decodeState pre.c1_root,SelectedSourceRecords.records cs bound)) ∧
      (∀ recoverC2, Reading recoverC2 sem values (tableBefore emptyTable tr target) H
        (SelectedSourceRecords.records cs bound)) ∧
      ∀ (whole : List (Addr SelectedTranscriptParams.L × State)) (Qtot : Nat),
        (∀ q ∈ tr, q ∈ whole) → (∀ q ∈ whole, q.2 = H q.1) →
        firstReads emptyTable whole ≤ Qtot →
        (¬ hitsBad (badColl SelectedTranscriptParams.params Qtot) emptyTable whole) →
        UnifiedSemanticRecovery.typed SelectedTranscriptParams.params
          (SourceDigestAddresses.rawBytes (alloc.vec.Vec.deref publicBytes))
          (tableBefore emptyTable whole target) 25 (decodeState t25.state) =
            some (decodeState pre.c1_root,SelectedSourceRecords.records cs bound) ∧
        Read whole target ∧
        (∀ recoverC2, Reading recoverC2 sem values (tableBefore emptyTable whole target) H
          (SelectedSourceRecords.records cs bound)) := by
  obtain ⟨sem,pre,initial,t25,cs,bound,values,publicBytes,wire,record25,tag,output,
    run,hr,hq,hbytes,hdecode,hparse,hnew,hL,hpub,hstate,hrecord,htag,targetBound,hdigest⟩ :=
    first_inputs invalidAccountData T P R B D mark error asf8 proof k out h
  obtain ⟨length,target,tr,htarget,htr,hlen,hcons,ha,htyped,hwhole⟩ :=
    SourceCanonicalRecovery.recover D () pre initial t25 (alloc.vec.Vec.deref publicBytes)
      pre.c1_root hnew hL hpub cs run hr bound tag record25.framed targetBound output hdigest
  refine ⟨sem,pre,initial,t25,cs,bound,values,publicBytes,record25,tag,output,
    run,hr,hq,hbytes,hdecode,hstate,hrecord,htag,hdigest,hL,targetBound,length,target,tr,
    htarget,htr,hlen,hcons,ha,htyped,?_,?_⟩
  · intro recoverC2
    exact completed_read D pre initial t25 cs run hr bound sem hq values hdecode
      (alloc.vec.Vec.deref publicBytes) pre.c1_root length (Subsingleton.elim _ _) recoverC2
      (tableBefore emptyTable tr target) (fun a v hv => (DuplexPrefixTable.table_consistent _ tr hcons target a v hv).1)
  · intro whole Qtot included consistent budget nohit
    obtain ⟨typed,read⟩ := hwhole whole Qtot included consistent budget nohit
    refine ⟨typed,read,?_⟩
    intro recoverC2
    exact completed_read D pre initial t25 cs run hr bound sem hq values hdecode
      (alloc.vec.Vec.deref publicBytes) pre.c1_root length (Subsingleton.elim _ _) recoverC2
      (tableBefore emptyTable whole target) (fun a v hv => (DuplexPrefixTable.table_consistent _ whole consistent target a v hv).1)

#print axioms first_inputs
#print axioms completed_read
#print axioms semantic_frame_bound
#print axioms first_typed
end AspisR1PublicPreparation.SourceFirstTyped
end
