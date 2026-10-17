import AspisR1.PoseidonClosure2GroupSlices
import ExtractedMaskQmPackBase4Whole

set_option autoImplicit false
namespace AspisR1.PoseidonClosure2PackGroup
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

abbrev QM := field.QM31
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev MappedPack := AspisR1.ExtractedMaskQmPackBase4Arithmetic.mathematicalPack

 theorem pack_group_success (a : Array QM 16#usize) (group : Usize)
    (hg : group.val < 4)
    (ha : ∀ i : Fin 16, Canonical (a.val[i.val]'(by simpa [a.property] using i.isLt))) :
    ∃ start finish : Usize, ∃ s : Slice QM, ∃ packed : QM, ∃ hlen : s.length = 4,
      start.val = 4 * group.val ∧ finish.val = start.val + 4 ∧ finish.val ≤ 16 ∧
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeUsizeSlice QM)) a
        { start, «end» := finish } = .ok s ∧
      field.qm31_pack_base4 s = .ok packed ∧ Canonical packed ∧
      AspisR1.ExtractedMaskQM31Exact.decode packed =
        MappedPack (AspisR1.ExtractedMaskQmPackBase4Whole.inputAt s hlen) := by
  obtain ⟨start, finish, hslice, hstart, hfinish, hbound⟩ :=
    AspisR1.PoseidonClosure2GroupSlices.source_slice_read a group hg
  let s := AspisR1.PoseidonClosure2GroupSlices.sliceAt a start finish
  have hstartle : start.val ≤ finish.val := by rw [hfinish]; omega
  have hlen : s.length = 4 := by
    change (a.val.slice start.val finish.val).length = 4
    exact AspisR1.PoseidonClosure2GroupSlices.slice_length_four a start finish hstartle hbound hfinish
  have hcan : ∀ j : Fin 4, Canonical
      (AspisR1.ExtractedMaskQmPackBase4Whole.inputAt s hlen j) := by
    intro j
    exact AspisR1.PoseidonClosure2GroupSlices.slice_canonical a start finish hstartle hbound hfinish ha j
  obtain ⟨packed,hpack,hpacked,hmodel⟩ :=
    AspisR1.ExtractedMaskQmPackBase4Whole.qm31_pack_base4_success s hlen hcan
  refine ⟨start,finish,s,packed,hlen,hstart,hfinish,hbound,?_,hpack,hpacked,hmodel⟩
  simpa [s] using hslice

#print axioms pack_group_success
end AspisR1.PoseidonClosure2PackGroup
