import JFr_TX2_Windows
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFr_TX2_ScalarRead
open Aeneas Aeneas.Std Result
open MultiproofConeSlices

/-- Exact scalar-read prefix of four_dots_one_loop0_loop0.body. -/
def read (q : Array U8 608#usize) (slot term : Usize) : Result U32 := do
  let i ← slot * 120#usize
  let i1 ← term * 4#usize
  let i2 ← i + i1
  let i3 ← i + i1
  let i4 ← i3 + 4#usize
  let s ← core.array.Array.index (core.ops.index.IndexSlice
    (core.slice.index.SliceIndexRangeUsizeSlice U8)) q {start:=i2,«end»:=i4}
  let r ← core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 s
  let a ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
  let o ← FIp_DotDecode.field.M31.from_le_bytes a
  core.option.Option.unwrap o

theorem source (q : Array U8 608#usize) (slot term : Usize)
    (hs : slot.val<4) (ht : term.val<26) (a : Array U8 4#usize) (v : U32)
    (window : (q.val.drop (120*slot.val+4*term.val)).take 4=a.val)
    (decode : FIp_DotDecode.field.M31.from_le_bytes a=ok (some v)) :
    read q slot term=ok v := by
  let off : Usize := Usize.ofNat (120*slot.val+4*term.val) (by scalar_tac)
  let stop : Usize := Usize.ofNat (120*slot.val+4*term.val+4) (by scalar_tac)
  let base : Usize := Usize.ofNat (120*slot.val) (by scalar_tac)
  let delta : Usize := Usize.ofNat (4*term.val) (by scalar_tac)
  have mul0 : slot*120#usize=ok base := by
    apply Port4A_ReaderInstall.mul_value
    change slot.val*120≤65536
    omega
  have mul1 : term*4#usize=ok delta := by
    apply Port4A_ReaderInstall.mul_value
    change term.val*4≤65536
    omega
  have add0 : base+delta=ok off := by
    have h := Port4A_ReaderInstall.add_value base delta (by change 120*slot.val+4*term.val≤65536;omega)
    exact h
  have add1 : off+4#usize=ok stop := Port4A_ReaderInstall.add_value _ _
    (by change 120*slot.val+4*term.val+4≤65536;omega)
  have range : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice U8)) q {start:=off,«end»:=stop}=ok (Array.to_slice a) := by
    change core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      (Array.to_slice q) {start:=off,«end»:=stop}=ok (Array.to_slice a)
    have h := range_total (Array.to_slice q) off stop
      (by change 120*slot.val+4*term.val≤120*slot.val+4*term.val+4;omega)
      (by change 120*slot.val+4*term.val+4≤q.val.length;rw [q.property];change _≤608;omega)
    have same : sub (Array.to_slice q) off stop=Array.to_slice a := by
      apply Subtype.ext
      simpa only [sub,List.slice,Array.to_slice,Nat.add_sub_cancel_left] using window
    exact h.trans (congrArg Result.ok same)
  unfold read
  rw [mul0,bind_tc_ok,mul1,bind_tc_ok,add0,bind_tc_ok,add1,bind_tc_ok,range,bind_tc_ok]
  have convert : core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8
      (Array.to_slice a)=ok (.Ok a) := by
    simp only [core.array.TryFromArrayCopySlice.try_from,Array.to_slice,a.property]
    rfl
  rw [convert,bind_tc_ok]
  simp only [core.result.Result.unwrap,bind_tc_ok,decode,core.option.Option.unwrap]

#print axioms source
end AspisR1.JFr_TX2_ScalarRead
end
