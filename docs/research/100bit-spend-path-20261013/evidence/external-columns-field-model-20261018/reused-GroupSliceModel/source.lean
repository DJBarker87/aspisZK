import AspisR1.PoseidonClosure2GroupSlices
import ExtractedMaskQmPackBase4Whole

set_option autoImplicit false
namespace AspisR1.PoseidonGroupSliceModel
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
abbrev QM := field.QM31
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode

def cell16 (a : Array QM 16#usize) (group j : Fin 4) : QM :=
  a.val[4 * group.val + j.val]'(by
    have hg := group.isLt
    have hj := j.isLt
    have hlen : a.val.length = 16 := by simpa using a.property
    omega)

def packedGroup (a : Array QM 16#usize) (group : Fin 4) :=
  AspisR1.ExtractedMaskQmPackBase4Arithmetic.mathematicalPack (cell16 a group)

/-- A successful source range read fixes every pack input to the corresponding
four contiguous cells of the original array. No unrelated slice is supplied. -/
theorem source_slice_cells
    (a : Array QM 16#usize) (group : Usize) (hg : group.val < 4)
    (start finish : Usize) (s : Slice QM) (hlen : s.length = 4)
    (hstart : start.val = 4 * group.val)
    (hfinish : finish.val = start.val + 4) (hbound : finish.val ≤ 16)
    (hread : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice QM)) a
      { start, «end» := finish } = .ok s) :
    ∀ j : Fin 4, AspisR1.ExtractedMaskQmPackBase4Whole.inputAt s hlen j =
      cell16 a ⟨group.val,hg⟩ j := by
  obtain ⟨start',finish',hread',hstart',hfinish',hbound'⟩ :=
    AspisR1.PoseidonClosure2GroupSlices.source_slice_read a group hg
  have hs : start' = start := by apply UScalar.eq_of_val_eq; omega
  have hf : finish' = finish := by apply UScalar.eq_of_val_eq; omega
  subst start'
  subst finish'
  rw [hread] at hread'
  have heq : s = AspisR1.PoseidonClosure2GroupSlices.sliceAt a start finish :=
    Result.ok.inj hread'
  subst s
  intro j
  have hle : start.val ≤ finish.val := by omega
  have hc := AspisR1.PoseidonClosure2GroupSlices.slice_input_eq
    a start finish hle hbound hfinish j
  simpa only [AspisR1.ExtractedMaskQmPackBase4Whole.inputAt,
    AspisR1.PoseidonClosure2GroupSlices.inputAt,cell16,hstart] using hc

theorem source_pack_model
    (a : Array QM 16#usize) (group : Usize) (hg : group.val < 4)
    (start finish : Usize) (s : Slice QM) (hlen : s.length = 4) (packed : QM)
    (hstart : start.val = 4 * group.val)
    (hfinish : finish.val = start.val + 4) (hbound : finish.val ≤ 16)
    (hread : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice QM)) a
      { start, «end» := finish } = .ok s)
    (hmodel : Decode packed =
      AspisR1.ExtractedMaskQmPackBase4Arithmetic.mathematicalPack
        (AspisR1.ExtractedMaskQmPackBase4Whole.inputAt s hlen)) :
    Decode packed = packedGroup a ⟨group.val,hg⟩ := by
  have heq : AspisR1.ExtractedMaskQmPackBase4Whole.inputAt s hlen =
      cell16 a ⟨group.val,hg⟩ := by
    funext j
    exact source_slice_cells a group hg start finish s hlen hstart hfinish hbound hread j
  simpa only [heq,packedGroup] using hmodel

#print axioms source_slice_cells
#print axioms source_pack_model
end AspisR1.PoseidonGroupSliceModel
