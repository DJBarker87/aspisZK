import NDO_JFy_SelectorExpand
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_SelectorSlices
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
def prefixSlice (point : Array NQ 10#usize) : Slice NQ :=
  ⟨point.val.slice 0 6, by
    have hmax : 4294967295 ≤ Usize.max := Usize.cMax_bound_concrete.1
    rw [List.slice_length]
    simp [point.property]
    omega⟩

def suffixSlice (point : Array NQ 10#usize) : Slice NQ :=
  ⟨point.val.drop 6, by
    have hmax : 4294967295 ≤ Usize.max := Usize.cMax_bound_concrete.1
    simp [point.property]
    omega⟩

theorem prefix_read (point : Array NQ 10#usize) :
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice NQ)) point
      ({ «end» := 6#usize } : core.ops.range.RangeTo Usize) = .ok (prefixSlice point) := by
  rw [Array.index_SliceIndexRangeToUsizeSlice]
  simp [core.slice.index.SliceIndexRangeToUsizeSlice.index,
    Array.to_slice, Slice.length, prefixSlice, List.slice_length,
    point.property]

theorem suffix_read (point : Array NQ 10#usize) :
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeFromUsizeSlice NQ)) point
      ({ start := 6#usize } : core.ops.range.RangeFrom Usize) = .ok (suffixSlice point) := by
  rw [Array.index_SliceIndexRangeFromUsizeSlice]
  simp [core.slice.index.SliceIndexRangeFromUsizeSlice.index,
    Array.to_slice, Slice.length, Slice.drop, suffixSlice, point.property]

theorem prefix_coordinates_canonical (point : Array NQ 10#usize)
    (hpoint : (∀ i : Fin (10#usize).val,Canon (point.val[i.val]'(by simpa only [point.property] using i.isLt)))) :
    ∀ x ∈ (prefixSlice point).val, Canon x := by
  have hlen : (prefixSlice point).val.length = 6 := by
    simp [prefixSlice, List.slice_length, point.property]
  have h10val : (10#usize).val = 10 := by scalar_tac
  have hpointLen : point.val.length = 10 := by simpa [h10val] using point.property
  intro x hx
  rcases List.mem_iff_getElem.mp hx with ⟨i, hi, hxi⟩
  rw [← hxi]
  have hi6 : i < 6 := by simpa [hlen] using hi
  have hidx10 : i < (10#usize).val := by simpa [h10val] using (show i < 10 by omega)
  have hidxPoint : i < point.val.length := by
    rw [hpointLen]
    simpa [h10val] using hidx10
  have hs : (prefixSlice point).val[i] = point.val[i] := by
    change (point.val.slice 0 6)[i] = point.val[i]
    calc
      (point.val.slice 0 6)[i] = point.val[0+i] :=
        List.getElem_slice 0 6 i point.val (by constructor <;> omega)
      _ = point.val[i] := by simp
  rw [hs]
  exact hpoint ⟨i, hidx10⟩

theorem suffix_coordinates_canonical (point : Array NQ 10#usize)
    (hpoint : (∀ i : Fin (10#usize).val,Canon (point.val[i.val]'(by simpa only [point.property] using i.isLt)))) :
    ∀ x ∈ (suffixSlice point).val, Canon x := by
  have hlen : (suffixSlice point).val.length = 4 := by
    simp [suffixSlice, point.property]
  have h10val : (10#usize).val = 10 := by scalar_tac
  have hpointLen : point.val.length = 10 := by simpa [h10val] using point.property
  intro x hx
  rcases List.mem_iff_getElem.mp hx with ⟨i, hi, hxi⟩
  rw [← hxi]
  have hi4 : i < 4 := by simpa [hlen] using hi
  have hidx : 6+i < 10 := by omega
  have hidxFin : 6+i < (10#usize).val := by simpa [h10val] using hidx
  have hidxPoint : 6+i < point.val.length := by
    rw [hpointLen]
    simpa [h10val] using hidxFin
  have hs : (suffixSlice point).val[i] = point.val[6+i] := by
    change (point.val.drop 6)[i] = point.val[6+i]
    exact List.getElem_drop
  rw [hs]
  exact hpoint ⟨6+i, hidxFin⟩


#print axioms prefix_read
#print axioms suffix_read
#print axioms prefix_coordinates_canonical
#print axioms suffix_coordinates_canonical
end AspisR1.JFy_SelectorSlices
end
