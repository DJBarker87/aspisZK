import RPu_FJh_GroupRange
import ExtractedMaskTowerAdd

set_option autoImplicit false
namespace AspisR1.FJh_GroupSlices
open Aeneas Aeneas.Std Result WP
open FIq_Native

abbrev QM := field.QM31
abbrev Canonical := FIv_NativeValue.Canon

def sliceAt (a : Array QM 16#usize) (start finish : Usize) : Slice QM :=
  ⟨a.val.slice start.val finish.val, by
    have hmax := Usize.cMax_bound_concrete.1
    rw [List.slice_length]
    simp [a.property]
    scalar_tac⟩

theorem slice_length_four (a : Array QM 16#usize) (start finish : Usize)
    (hstart : start.val ≤ finish.val) (hbound : finish.val ≤ 16)
    (hfinish : finish.val = start.val + 4) :
    (a.val.slice start.val finish.val).length = 4 := by
  have hlen : a.val.length = 16 := by simpa using a.property
  rw [List.slice_length]
  rw [hlen, hfinish]
  have hspan : start.val + 4 - start.val = 4 := by omega
  rw [hspan]
  have hremaining : 4 ≤ 16 - start.val := by omega
  rw [Nat.min_eq_right hremaining]

def inputAt (a : Array QM 16#usize) (start finish : Usize)
    (hfinish : finish.val = start.val + 4) (hbound : finish.val ≤ 16)
    (j : Fin 4) : QM :=
  a.val[(start.val + j.val)]'(by
    have hlen : a.val.length = 16 := by simpa using a.property
    change start.val + j.val < a.val.length
    rw [hlen]
    omega)

theorem source_slice_read (a : Array QM 16#usize) (group : Usize)
    (hg : group.val < 4) :
    ∃ start finish : Usize,
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeUsizeSlice QM)) a
        { start, «end» := finish } = .ok (sliceAt a start finish) ∧
      start.val = 4 * group.val ∧ finish.val = start.val + 4 ∧
      finish.val ≤ 16 := by
  obtain ⟨start,finish,hrun,hstart,hfinish,hbound⟩ :=
    AspisR1.FJh_GroupRange.group_range_success group hg
  refine ⟨start, finish, ⟨?read, hstart, ?hend, hbound⟩⟩
  · rw [Array.index_SliceIndexRangeUsizeSlice]
    simp only [core.slice.index.SliceIndexRangeUsizeSlice.index]
    have hle : start.val ≤ finish.val := by rw [hfinish]; omega
    have hlen : finish.val ≤ (a.val.length) := by
      have ha : a.val.length = 16 := by simpa using a.property
      rw [ha]
      exact hbound
    simp [Array.to_slice, Slice.length, hle, hlen, sliceAt]
    exact hbound
  · rw [hstart]
    omega

theorem slice_input_eq (a : Array QM 16#usize) (start finish : Usize)
    (hstart : start.val ≤ finish.val) (hbound : finish.val ≤ 16)
    (hfinish : finish.val = start.val + 4) (j : Fin 4) :
    (sliceAt a start finish).val[j.val]'(by
      have hs : (sliceAt a start finish).length = 4 := by
        change (a.val.slice start.val finish.val).length = 4
        exact slice_length_four a start finish hstart hbound hfinish
      change j.val < (sliceAt a start finish).length
      rw [hs]
      exact j.isLt) = inputAt a start finish hfinish hbound j := by
  have hs : (sliceAt a start finish).length = 4 := by
    change (a.val.slice start.val finish.val).length = 4
    exact slice_length_four a start finish hstart hbound hfinish
  have hidx : j.val < (sliceAt a start finish).length := by
    change j.val < (sliceAt a start finish).length
    rw [hs]
    exact j.isLt
  change (a.val.slice start.val finish.val)[j.val]'(by
    change j.val < (sliceAt a start finish).length
    exact hidx) = _
  rw [List.getElem_slice start.val finish.val j.val a.val]
  simp [inputAt]
  have hlen : a.val.length = 16 := by simpa using a.property
  rw [hlen] at *
  constructor <;> omega

#print axioms slice_length_four
#print axioms source_slice_read
#print axioms slice_input_eq
end AspisR1.FJh_GroupSlices
