import ExtractedFirstPairedReachability
import R1SemanticPrefixCompletedAgreement
import AspisV8R19.SqueezeOracleBridge
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.SelectedSourceRecords
open FS FS2 FS2.Duplex AspisV8R19.SourceDuplexStep
open AspisR1 AspisV8R19.SqueezeOracleBridge

abbrev Message := SelectedTranscriptParams.Message

def message {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    (c : SourceFull25.Call D pre)
    (bound : (c.record.framed.val.map ExtractedRecordByteValue.rawByte).length ≤ 901) : Message :=
  ⟨c.record.framed.val.map ExtractedRecordByteValue.rawByte, by
    change (c.record.framed.val.map ExtractedRecordByteValue.rawByte).length ≤ 3717
    omega⟩

/-- The selected records are constructed from the exact reached Call list.
Their before/absorb/after states use the accepted fixed32-byte representation. -/
def records {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    (cs : List (SourceFull25.Call D pre))
    (bound : ∀ c ∈ cs, (c.record.framed.val.map ExtractedRecordByteValue.rawByte).length ≤ 901) :
    List (Rec Message) :=
  cs.attach.map (fun c =>
    (decodeState c.val.before.state, decodeState c.val.absorbed,
      message c.val (bound c.val c.property), decodeState c.val.after.state))

theorem records_bytes {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    (cs : List (SourceFull25.Call D pre))
    (bound : ∀ c ∈ cs, (c.record.framed.val.map ExtractedRecordByteValue.rawByte).length ≤ 901) :
    (records cs bound).map (fun r => r.2.2.1.val) = SourceFull25.rawFrames cs := by
  simp [records, message, SourceFull25.rawFrames, List.map_map, Function.comp_def]

/-- Strict decoding of the exact source-constructed bounded selected records.
This is not yet recovered-log/table/init/typed-context provenance. -/
theorem first_records {E : Type} (invalidAccountData : E)
    (T : Tx1Model.Boundaries) (P : PreparedModel.Boundaries)
    (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    (D : aspis_core.Digest32 Unit)
    (mark : FirstCaller.Phase → Result Unit) (error : verifier.Error → Result E)
    (asf8 proof : Slice U8) (k : Usize) (out : alloc.vec.Vec U8)
    (h : FirstCaller.first invalidAccountData
      (FirstHelperBinding.tx1 T P (FinishModel.finish R B) D) mark error asf8 proof k =
        ok (.Ok out)) :
    ∃ pre initial t25, ∃ cs : List (SourceFull25.Call D pre),
      ∃ bound : (∀ c ∈ cs, (c.record.framed.val.map ExtractedRecordByteValue.rawByte).length ≤ 901),
      ∃ values : SemanticPrefixCodec.Full,
        SourceFull25.Trace D pre initial t25 cs ∧
        cs.map SourceFull25.Call.row = ActualFull25.rows ∧
        (records cs bound).map (fun r => r.2.2.1.val) = PrefixAdapter.completedRecords pre ∧
        SemanticPrefixCodec.decodeFrom 0 ((records cs bound).map (fun r => r.2.2.1.val)) =
          some (SemanticPrefixCodec.entriesOf values) := by
  obtain ⟨s,supplied,view,sem,pre,initial,t25,hd,heq,hv,hp,hh,hstate,
    cs,values,ht,hr,hq,hbytes,hdecode,hbound⟩ :=
    ActualFull25.first_full25 invalidAccountData T P R B D mark error asf8 proof k out h
  refine ⟨pre,initial,t25,cs,hbound,values,ht,hr,?_,?_⟩
  · rw [records_bytes]; exact hbytes
  · rw [records_bytes]; exact hdecode

/-- The read premise is supplied by the exact reached source frames and their
strict parser result. The oracle remains explicit: correspondence of these
completed challenges with actual source QM31 samples is a separate finite
source/oracle obligation, not inferred by choosing a table or a C2 witness. -/
theorem first_completed_read {E : Type} (invalidAccountData : E)
    (T : Tx1Model.Boundaries) (P : PreparedModel.Boundaries)
    (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    (D : aspis_core.Digest32 Unit)
    (mark : FirstCaller.Phase → Result Unit) (error : verifier.Error → Result E)
    (asf8 proof : Slice U8) (k : Usize) (out : alloc.vec.Vec U8)
    (oracle : Addr SelectedTranscriptParams.L → State)
    (recoverC2 : State → SemanticPayloadView.InitialWord × SemanticPayloadView.InitialWord)
    (h : FirstCaller.first invalidAccountData
      (FirstHelperBinding.tx1 T P (FinishModel.finish R B) D) mark error asf8 proof k =
        ok (.Ok out)) :
    ∃ pre initial t25, ∃ cs : List (SourceFull25.Call D pre),
      ∃ bound : (∀ c ∈ cs, (c.record.framed.val.map ExtractedRecordByteValue.rawByte).length ≤ 901),
      ∃ values : SemanticPrefixCodec.Full,
        SourceFull25.Trace D pre initial t25 cs ∧
        cs.map SourceFull25.Call.row = ActualFull25.rows ∧
        (records cs bound).map (fun r => r.2.2.1.val) = PrefixAdapter.completedRecords pre ∧
        SelectedSemanticPrefix.read recoverC2 0
          (SelectedCompletedSemantic.pairs emptyTable oracle 0 (records cs bound)) =
          some (((SemanticPrefixCodec.entriesOf values).map
            (fun e => SemanticPayloadView.toMessage recoverC2 e.2.value.val)).zip
              ((SelectedCompletedSemantic.pairs emptyTable oracle 0 (records cs bound)).map Prod.snd)) := by
  obtain ⟨pre,initial,t25,cs,bound,values,ht,hr,hbytes,hdecode⟩ :=
    first_records invalidAccountData T P R B D mark error asf8 proof k out h
  exact ⟨pre,initial,t25,cs,bound,values,ht,hr,hbytes,
    SemanticPrefixCompletedAgreement.completed_read_of_decode recoverC2 emptyTable oracle
      0 (records cs bound) (SemanticPrefixCodec.entriesOf values) hdecode⟩

#print axioms message
#print axioms records
#print axioms records_bytes
#print axioms first_records
#print axioms first_completed_read
end AspisR1PublicPreparation.SelectedSourceRecords
