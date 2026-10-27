import SAQ_Decoder
import RPt_JFo_Opening
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFo_QueryRead
open Aeneas Aeneas.Std Result
open MultiproofConeSlices

theorem source (bytes : Slice U8) (i : Usize) (inside : i.val<4)
    (size : bytes.val.length=832) (arr : Array U8 32#usize)
    (value : AspisR1RecordParser.field.wide_exact.WideExact)
    (selected : (bytes.val.drop (32*i.val)).take 32=arr.val)
    (decoded : AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes
      (Array.to_slice arr)=ok (some value)) :
    SAQ_Decoder.read bytes i=ok (SAQ_RecordDecode.fromRecord value) := by
  let start : Usize := Usize.ofNat (32*i.val) (by scalar_tac)
  let stop : Usize := Usize.ofNat (32*i.val+32) (by scalar_tac)
  have startVal : start.val=32*i.val := rfl
  have stopVal : stop.val=32*i.val+32 := rfl
  have hs : 32#usize*i=ok start := Port4A_ReaderInstall.mul_value _ _ (by change 32*i.val≤65536;omega)
  have he : start+32#usize=ok stop := Port4A_ReaderInstall.add_value _ _ (by change 32*i.val+32≤65536;omega)
  have range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      bytes {start:=start,«end»:=stop}=ok (Array.to_slice arr) := by
    have run := range_total bytes start stop (by change 32*i.val≤32*i.val+32;omega)
      (by change 32*i.val+32≤bytes.val.length;omega)
    have same : sub bytes start stop=Array.to_slice arr := by
      apply Subtype.ext
      simpa only [sub,List.slice,startVal,stopVal,Array.to_slice,Nat.add_sub_cancel_left] using selected
    exact run.trans (congrArg Result.ok same)
  simp only [SAQ_Decoder.read,hs,he,range,decoded,bind_tc_ok,
    core.option.Option.unwrap]
  rfl

#print axioms source
end AspisR1.JFo_QueryRead
end
