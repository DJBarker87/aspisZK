import ExtractedSelectedSourceAgreement
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.SourceReadFromFirst
open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisR1 SelectedSourceRecords SelectedSourceAgreement

/-- Actual first success supplies the read premise and exact source challenges
for every table consistent with the oracle constructed from that same D and
actual initializer. C2 interpretation is an explicit callback; no word custody
or already-read typed-log success is inferred from this result. -/
theorem first_source_read {E : Type} (invalidAccountData : E)
    (T : Tx1Model.Boundaries) (P : PreparedModel.Boundaries)
    (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    (D : aspis_core.Digest32 Unit)
    (mark : FirstCaller.Phase → Result Unit) (error : verifier.Error → Result E)
    (asf8 proof : Slice U8) (k : Usize) (out : alloc.vec.Vec U8)
    (recoverC2 : State → SemanticPayloadView.InitialWord × SemanticPayloadView.InitialWord)
    (h : FirstCaller.first invalidAccountData
      (FirstHelperBinding.tx1 T P (FinishModel.finish R B) D) mark error asf8 proof k =
        ok (.Ok out)) :
    ∃ (sem : r1_semantic.Verified Unit) (pre : r1_wire.Prefix)
      (initial t25 : r1_wire.SemanticTranscript Unit),
      ∃ cs : List (SourceFull25.Call D pre),
      ∃ bound : (∀ c ∈ cs, (c.record.framed.val.map ExtractedRecordByteValue.rawByte).length ≤ 901),
      ∃ (values : SemanticPrefixCodec.Full) (bytes : alloc.vec.Vec U8) (wire : SemanticPublicWire.Wire)
        (length : U32),
        SourceFull25.Trace D pre initial t25 cs ∧
        cs.map SourceFull25.Call.row = ActualFull25.rows ∧
        cs.map SourceFull25.Call.q = BeginCalls.challengeList sem.challenges ++ sem.alpha.val ∧
        SourceFull25.rawFrames cs = PrefixAdapter.completedRecords pre ∧
        SemanticPublicWire.parsePublic (bytes.val.map AspisR1PublicSerializer.RawBridge431.rawByte) =
          some (SemanticPublicWire.toPublic wire) ∧
        r1_wire.SemanticTranscript.new D () (alloc.vec.Vec.deref bytes) pre.c1_root = ok (.Ok initial) ∧
        ∃ hL : 75 + (SourceDigestAddresses.rawBytes (alloc.vec.Vec.deref bytes)).length ≤
          SelectedTranscriptParams.L,
        let H : Addr SelectedTranscriptParams.L → State :=
          SourceDigestOracle.oracle D () (alloc.vec.Vec.deref bytes) pre.c1_root length
        decodeState initial.state = H (PublicInitFrame.addr
          (SourceDigestAddresses.rawBytes (alloc.vec.Vec.deref bytes)) hL (decodeState pre.c1_root)) ∧
        ∀ table : Table (Addr SelectedTranscriptParams.L) State,
          (∀ a v, table a = some v → v = H a) →
          SelectedSemanticPrefix.read recoverC2 0
            (SelectedCompletedSemantic.pairs table H 0 (records cs bound)) =
              some (((SemanticPrefixCodec.entriesOf values).map
                (fun e => SemanticPayloadView.toMessage recoverC2 e.2.value.val)).zip
                  ((BeginCalls.challengeList sem.challenges ++ sem.alpha.val).map sourceChallenge)) ∧
          R0P.Mask.semChalsZ (SelectedSemanticPrefixFacts.lift
            (((SemanticPrefixCodec.entriesOf values).map
              (fun e => SemanticPayloadView.toMessage recoverC2 e.2.value.val)).zip
                ((BeginCalls.challengeList sem.challenges ++ sem.alpha.val).map sourceChallenge))) =
            some ((BeginCalls.challengeList sem.challenges ++ sem.alpha.val).map sourceChallenge) := by
  obtain ⟨s,supplied,view,sem,pre,initial,t25,hd,heq,hv,hp,hh,hstate,
    cs,values,run,hr,hq,hbytes,hdecode,bound⟩ :=
    ActualFull25.first_full25 invalidAccountData T P R B D mark error asf8 proof k out h
  have hh' : r1_semantic.public_transcript D (PreparationBinding.preparationPublic s) ()
      pre.c1_root = ok (.Ok initial) := heq ▸ hh
  obtain ⟨bytes,wire,hs,hw,hparse,hn⟩ :=
    PreparationBinding.decoder_helper_parsePublic D asf8 s () pre.c1_root initial hd hh'
  obtain ⟨length,state,hlen,hdigest,hout⟩ := TranscriptStep.new_success D ()
    (alloc.vec.Vec.deref bytes) pre.c1_root initial hn
  have hfit := SemanticPublicCodecComplete.parsed_init_fits _ _ hparse
  have hL : 75 + (SourceDigestAddresses.rawBytes (alloc.vec.Vec.deref bytes)).length ≤
      SelectedTranscriptParams.L := by
    have hsmall : 75 + (SourceDigestAddresses.rawBytes (alloc.vec.Vec.deref bytes)).length ≤ 1530 := by
      simpa only [SourceDigestAddresses.rawBytes, alloc.vec.Vec.deref, List.length_map] using hfit
    dsimp only [SelectedTranscriptParams.L]
    omega
  have hinit := SourceDigestOracle.oracle_at D () (alloc.vec.Vec.deref bytes)
    pre.c1_root length .initial (PublicInitFrame.addr
      (SourceDigestAddresses.rawBytes (alloc.vec.Vec.deref bytes)) hL (decodeState pre.c1_root)) state
    (SourceDigestAddresses.init_address _ _ _
      (SourceDigestAddresses.successful_length _ _ hlen) hL) hdigest
  refine ⟨sem,pre,initial,t25,cs,bound,values,bytes,wire,length,run,hr,hq,hbytes,hparse,hn,hL,?_,?_⟩
  · simpa only [hout] using hinit
  · intro table htable
    have hhash : initial.hash = () := by rw [hout]
    have hqs := source_completed_qs cs run hr bound (alloc.vec.Vec.deref bytes)
      pre.c1_root length table (by simpa only [hhash] using htable)
    rw [hhash] at hqs
    have hactual : cs.map (fun c => sourceChallenge c.q) =
        (BeginCalls.challengeList sem.challenges ++ sem.alpha.val).map sourceChallenge := by
      simpa only [List.map_map, Function.comp_def] using congrArg (List.map sourceChallenge) hq
    have hqfinal := hqs.trans hactual
    have hdec : SemanticPrefixCodec.decodeFrom 0 ((records cs bound).map (fun r => r.2.2.1.val)) =
        some (SemanticPrefixCodec.entriesOf values) := by rw [records_bytes]; exact hdecode
    have hread := SemanticPrefixCompletedAgreement.completed_read_of_decode recoverC2 table
      (SourceDigestOracle.oracle D () (alloc.vec.Vec.deref bytes) pre.c1_root length)
      0 (records cs bound) (SemanticPrefixCodec.entriesOf values) hdec
    rw [hqfinal] at hread
    refine ⟨hread, ?_⟩
    simpa only [hqfinal] using SelectedCompletedSemantic.semChalsZ_read recoverC2 0 table
      (SourceDigestOracle.oracle D () (alloc.vec.Vec.deref bytes) pre.c1_root length)
      (records cs bound) _ hread

#print axioms first_source_read
end AspisR1PublicPreparation.SourceReadFromFirst
end
