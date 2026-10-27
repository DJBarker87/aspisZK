import RPt_JFr_TX2_Windows
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFr_TX2_TailRead
open Aeneas Aeneas.Std Result
open MultiproofConeSlices
abbrev Q := FIo_Native.aspis_core.field.QM31

/-- Actual physical range and QM31 decode used at each of the three tail sites. -/
def read (q : Array U8 608#usize) (start stop : Usize) : Result Q := do
  let s ← core.array.Array.index (core.ops.index.IndexSlice
    (core.slice.index.SliceIndexRangeUsizeSlice U8)) q {start:=start,«end»:=stop}
  let value ← FIp_DotDecode.field.QM31.from_le_bytes s
  core.option.Option.unwrap value

theorem source (q : Array U8 608#usize) (start stop : Usize)
    (span : stop.val=start.val+16) (bound : stop.val≤608)
    (a : Array U8 16#usize) (v : Q)
    (window : (q.val.drop start.val).take 16=a.val)
    (decode : FIp_DotDecode.field.QM31.from_le_bytes (Array.to_slice a)=ok (some v)) :
    read q start stop=ok v := by
  have range : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice U8)) q {start:=start,«end»:=stop}=ok (Array.to_slice a) := by
    change core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      (Array.to_slice q) {start:=start,«end»:=stop}=ok (Array.to_slice a)
    have h := range_total (Array.to_slice q) start stop (by omega)
      (by change stop.val≤q.val.length;rw [q.property];exact bound)
    have same : sub (Array.to_slice q) start stop=Array.to_slice a := by
      apply Subtype.ext
      simpa only [sub,List.slice,Array.to_slice,span,Nat.add_sub_cancel_left] using window
    exact h.trans (congrArg Result.ok same)
  simp only [read,range,decode,bind_tc_ok,core.option.Option.unwrap]
  rfl

#print axioms source
end AspisR1.JFr_TX2_TailRead
end
