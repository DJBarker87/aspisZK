import F3P_TraceParsed
set_option autoImplicit false
namespace AspisR1.F3P_TracePayload
open Aeneas Aeneas.Std Result AspisR1DecodeKFullValueTrace

theorem bytes (r : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (byteOffset j offset : Usize) (q : QM) (t : ParserTrace r byteOffset j offset q) :
    (ParserTrace.payloadData t).val=r.framed.val.drop 5 := by
  have source := ParserTrace.hpayload t
  unfold AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.payload at source
  simp only [Slice.index_SliceIndexRangeFromUsizeSliceInst] at source
  unfold core.slice.index.SliceIndexRangeFromUsizeSlice.index at source
  split at source
  · have same := congrArg Subtype.val (Result.ok.inj source)
    exact same.symm
  · cases source

#print axioms bytes
end AspisR1.F3P_TracePayload
