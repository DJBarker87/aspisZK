import S1ExtractedRoundChildrenV1
import FIq_S_RawActualDecodeKInitialLowClaim
import FIq_S_RawActualAnnotatedTypedRowReadback
import FIq_S_RecordFrameDropPayload
import R1SemanticPayloadView
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIq_TypedInitial
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1PublicPreparation.RawActualAnnotatedTypedRows
open AspisR1PublicPreparation.RawActualDecodeKPayloadBytes
open AspisR1PublicPreparation.RawActualDecodeKTypedCoefficients
open AspisR1PublicPreparation.RawActualDecodeKMainAdapter

theorem frame_at (pre : r1_wire.Prefix) (row : U8) (hr : row.val<25)
    (record : r1_wire.ValidatedRecord) (read : r1_wire.Prefix.validated_record pre row=ok (.Ok record))
    (values : SemanticPrefixCodec.Full) (full : SemanticPrefixCodec.encodeFull values=PrefixAdapter.completedRecords pre) :
    SemanticRecordCodec.encode (values ⟨row.val,hr⟩)=record.framed.val.map ExtractedRecordByteValue.rawByte := by
  have raw := (validated_record_bytes pre row record read).2
  have completed : (PrefixAdapter.completedRecords pre)[row.val]?=
      some (record.framed.val.map ExtractedRecordByteValue.rawByte) := by
    unfold PrefixAdapter.completedRecords
    rw [List.getElem?_map,List.getElem?_take_of_lt (l := pre.records.val) (i := row.val) (j := 25) hr,raw]
    rfl
  have encoded : (SemanticPrefixCodec.encodeFull values)[row.val]?=
      some (SemanticRecordCodec.encode (values ⟨row.val,hr⟩)) := by
    simp only [SemanticPrefixCodec.encodeFull,List.getElem?_map]
    rw [List.getElem?_eq_getElem (by rw [SemanticPrefixCodec.entriesOf_length];exact hr)]
    rw [SemanticPrefixCodec.entriesOf_getElem values ⟨row.val,hr⟩]
    rfl
  exact Option.some.inj (encoded.symm.trans ((congrArg (fun xs : List SemanticRecordCodec.Bytes => xs[row.val]?) full).trans completed))

theorem initial (pre : r1_wire.Prefix) (record : r1_wire.ValidatedRecord)
    (read : r1_wire.Prefix.validated_record pre 14#u8=ok (.Ok record))
    (decoded : Array AspisS1ExtractedRoundChildren.MainQM 1#usize)
    (initial : AspisS1ExtractedRoundChildren.MainQM)
    (decode : AspisS1ExtractedRoundChildren.decodeMain 1#usize record 0#usize=ok (.Ok decoded))
    (index : Array.index_usize decoded 0#usize=ok initial)
    (values : SemanticPrefixCodec.Full) (full : SemanticPrefixCodec.encodeFull values=PrefixAdapter.completedRecords pre) :
    algebraMap ExtractedMaskQM31Exact.QM31Exact AspisWideTower.WideExact
      (RawActualAnnotatedPolynomialRun.DecodeMain initial)=SemanticPayloadView.claimAt14 values := by
  have frame := frame_at pre 14#u8 (by decide) record read values full
  change SemanticRecordCodec.encode (values (14 : Fin 25))=_ at frame
  have payloadEq : ((payload record).map ExtractedRecordByteValue.rawByte)=
      SemanticCoefficientCodec.encodeLow (SemanticPayloadView.claimPayloadAt14 values) := by
    have dropEq := congrArg (fun xs : SemanticRecordCodec.Bytes => xs.drop 5) frame
    simpa only [SemanticRecordCodec.encode,SemanticPayloadView.claimAt14_payload,
      SemanticRecordCodec.payloadTag,SemanticRecordCodec.payloadBytes,RecordFrameDropPayload.drop_frame,
      payload,List.map_drop] using dropEq.symm
  have typed : SemanticCoefficientCodec.decodeLow ((payload record).map ExtractedRecordByteValue.rawByte)=
      some (SemanticPayloadView.claimPayloadAt14 values) := by
    rw [payloadEq]
    exact SemanticCoefficientCodec.decodeLow_encode _
  exact RawActualDecodeKInitialLowClaim.decodeMain_one_indexed_wide_value record decoded initial
    (SemanticPayloadView.claimPayloadAt14 values) decode index typed

#print axioms frame_at
#print axioms initial
end AspisR1.FIq_TypedInitial
end
