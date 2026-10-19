import BatchedWeightsNewSuccessContentsBoundsV3
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1BatchedWeightsExtraction
namespace BWVecSliceReadProbeV3
abbrev Row := Array Std.U64 4#usize
theorem probe (raw : alloc.vec.Vec Row) (i : Usize) (hi : i.val < raw.length) (r : Row)
    (h : Slice.index_usize (raw : Slice Row) i = .ok r) :
    raw.val[i.val]'hi = r := by
  change alloc.vec.Vec.index_usize raw i = .ok r at h
  unfold alloc.vec.Vec.index_usize at h
  cases hidx : raw[i.val]? with
  | none => simp [hidx] at h
  | some x =>
      simp only [hidx] at h
      injection h with hx
      subst x
      have h' : ((↑raw)[i.val]?) = some r := hidx
      rcases List.getElem?_eq_some_iff.mp h' with ⟨hb, heq⟩
      exact heq
end BWVecSliceReadProbeV3
