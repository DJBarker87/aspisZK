import Stage2ContinuationTypes
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1Stage2.WireTx2

theorem range_width (bytes out : Slice U8) (start finish : Usize)
    (h : core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes
      {start, «end» := finish} = ok out) :
    out.val.length = finish.val - start.val := by
  simp only [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index] at h
  split at h
  · rename_i hb
    have hv := congrArg (fun s : Slice U8 => s.val.length) (Result.ok.inj h)
    simp only [UScalar.le_equiv, Slice.length] at hb
    simp [List.slice] at hv
    omega
  · cases h

theorem prefix_width (bytes out : Slice U8) (finish : Usize)
    (h : core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeToUsizeSlice U8) bytes
      { «end» := finish} = ok out) : out.val.length = finish.val := by
  simp only [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index] at h
  split at h
  · rename_i hb
    have hv := congrArg (fun s : Slice U8 => s.val.length) (Result.ok.inj h)
    simp only [Slice.length] at hb
    simp [List.slice] at hv
    omega
  · cases h

theorem sibling_get_width (nodes sibling : Slice U8) (at1 finish : Usize)
    (add : at1 + 32#usize = ok finish)
    (get : core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice U8)
      nodes {start := at1, «end» := finish} = ok (some sibling)) :
    sibling.val.length = 32 := by
  have ha := (UScalar.add_equiv at1 32#usize)
  rw [add] at ha
  simp only [core.slice.Slice.get, core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.get] at get
  split at get
  · rename_i hb
    have he := Option.some.inj (Result.ok.inj get)
    have hv := congrArg (fun s : Slice U8 => s.val.length) he
    simp only [UScalar.le_equiv, Slice.length] at hb
    simp [List.slice] at hv
    have h32 : (32#usize).val = 32 := rfl
    rw [h32] at ha
    omega
  · cases get

/-- Exact checksum-prefix length from checked subtraction and slice success. -/
theorem checksum_body_width (bytes body : Slice U8) (finish : Usize)
    (size : bytes.val.length = 1768)
    (sub : Slice.len bytes - 32#usize = ok finish)
    (read : core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeToUsizeSlice U8) bytes
      { «end» := finish} = ok body) : body.val.length = 1736 := by
  have hs := UScalar.sub_equiv (Slice.len bytes) 32#usize
  rw [sub] at hs
  have hw := prefix_width bytes body finish read
  have hl : (Slice.len bytes).val = bytes.val.length := by rfl
  have h32 : (32#usize).val = 32 := rfl
  rw [hl, h32, size] at hs
  omega
#print axioms range_width
#print axioms prefix_width
#print axioms sibling_get_width
#print axioms checksum_body_width
end AspisR1Stage2.WireTx2
