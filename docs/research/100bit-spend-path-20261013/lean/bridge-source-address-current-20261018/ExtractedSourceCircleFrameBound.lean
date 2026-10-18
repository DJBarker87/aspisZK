import ExtractedPrefixParseCore
import ExtractedPrefixFrameAgreement
import ExtractedSourceFull25Frames

/-! The next actual row's size is supplied by the actual full Prefix parser,
not by the first25 frame bound or a separately chosen frame. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.SourceCircleFrameBound
open r1_wire AspisR1

theorem row25_length (bytes : Slice U8) (pre : Prefix) (record : ValidatedRecord)
    (hp : PrefixAdapter.parseAccepted bytes = ok (.Ok pre))
    (hr : Prefix.validated_record pre 25#u8 = ok (.Ok record)) :
    record.framed.val.length = 3717 := by
  have hparse := PrefixAdapter.parse_success bytes pre hp
  obtain ⟨hrow, hslot⟩ := SourceFull25.validated_record_bytes pre 25#u8 record hr
  have hmem : (25#u8, record.framed) ∈
      ExtractedPrefixTrace.rowOrder.zip (PrefixAdapter.toOld pre).records.val := by
    apply List.mem_of_getElem? (i := 25)
    apply List.getElem?_zip_eq_some.mpr
    exact ⟨rfl, hslot⟩
  obtain ⟨tag, size, payload, ht, hrecord, hlen, hframe, hmodel⟩ :=
    ExtractedPrefixFrameAgreement.prefix_record_frame_success bytes
      (PrefixAdapter.toOld pre) hparse 25#u8 record.framed hmem
  have hshape : ExtractedRowShape.table 25#u8 = some (4#u8, 3712#usize) := rfl
  have he : size = 3712#usize :=
    congrArg Prod.snd (Option.some.inj (ht.symm.trans hshape))
  subst size
  have hf := (RecordFrameCodec.parse_eq_some_iff _ _ _ _).mp hframe
  have hl := congrArg List.length hf.2
  have hsize : (3712#usize).val = 3712 := by scalar_tac
  simpa only [List.length_map, RecordFrameCodec.frame_length, hlen, hsize] using hl

#print axioms row25_length
end AspisR1PublicPreparation.SourceCircleFrameBound
