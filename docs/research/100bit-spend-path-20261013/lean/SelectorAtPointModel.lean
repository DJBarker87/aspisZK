import SelectorExpansionOldAdapter
import ExtractedMaskTowerAdd
import SelectorSourceSlice

/-! Checked source-to-model adapter for the actual `at_point` slice/evaluation
wrapper. The actual forward selector expansion and old descending-product
model are imported; this file derives the two ranges from one canonical
10-coordinate input and composes their bounded outputs. -/
set_option autoImplicit false
namespace AspisR1.SelectorAtPointModel

open Aeneas Aeneas.Std Result ControlFlow WP
open AspisR1SelectedMaskProbe
open AspisR1.SelectorExpansionCorrectness
open AspisR1.SelectorExpansionOuter
open AspisR1.SelectorExpansionOldAdapter
open AspisR1.ExtractedMaskTowerAdd

abbrev QM := field.QM31
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Canonical := AspisR1.ExtractedMaskTowerAdd.CanonicalQM

def exactPoint (point : Array QM 10#usize) (i : Nat) : ExactQM :=
  if h : i < 10 then decode (point.val[i]'(by simpa [point.property] using h)) else 0

def prefixSlice (point : Array QM 10#usize) : Slice QM :=
  ⟨point.val.slice 0 6, by
    have hmax : 4294967295 ≤ Usize.max := Usize.cMax_bound_concrete.1
    rw [List.slice_length]
    simp [point.property]
    omega⟩

def suffixSlice (point : Array QM 10#usize) : Slice QM :=
  ⟨point.val.drop 6, by
    have hmax : 4294967295 ≤ Usize.max := Usize.cMax_bound_concrete.1
    simp [point.property]
    omega⟩

private theorem prefix_read (point : Array QM 10#usize) :
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice QM)) point
      ({ «end» := 6#usize } : core.ops.range.RangeTo Usize) = .ok (prefixSlice point) := by
  rw [Array.index_SliceIndexRangeToUsizeSlice]
  simp [core.slice.index.SliceIndexRangeToUsizeSlice.index,
    Array.to_slice, Slice.length, prefixSlice, List.slice_length,
    point.property]

private theorem suffix_read (point : Array QM 10#usize) :
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeFromUsizeSlice QM)) point
      ({ start := 6#usize } : core.ops.range.RangeFrom Usize) = .ok (suffixSlice point) := by
  rw [Array.index_SliceIndexRangeFromUsizeSlice]
  simp [core.slice.index.SliceIndexRangeFromUsizeSlice.index,
    Array.to_slice, Slice.length, Slice.drop, suffixSlice, point.property]

private theorem prefix_coordinates_canonical (point : Array QM 10#usize)
    (hpoint : canonicalArray point) :
    ∀ x ∈ (prefixSlice point).val, Canonical x := by
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

private theorem suffix_coordinates_canonical (point : Array QM 10#usize)
    (hpoint : canonicalArray point) :
    ∀ x ∈ (suffixSlice point).val, Canonical x := by
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

private theorem prefix_exactCoordinates (point : Array QM 10#usize) (i : Nat)
    (hi : i < 6) : exactCoordinates (prefixSlice point).val i = exactPoint point i := by
  have hpoint : i < 10 := by omega
  have h10val : (10#usize).val = 10 := by scalar_tac
  have hpointLen : point.val.length = 10 := by simpa [h10val] using point.property
  simp [exactCoordinates, exactPoint, prefixSlice, hi, hpoint, List.getElem_slice,
    point.property]

private theorem suffix_exactCoordinates (point : Array QM 10#usize) (i : Nat)
    (hi : i < 4) : exactCoordinates (suffixSlice point).val i = exactPoint point (6+i) := by
  have hpoint : 6+i < 10 := by omega
  have h10val : (10#usize).val = 10 := by scalar_tac
  have hpointLen : point.val.length = 10 := by simpa [h10val] using point.property
  simp [exactCoordinates, exactPoint, suffixSlice, hi, hpoint,
    List.getElem_drop, point.property]

private theorem tensor_prefix (point : Array QM 10#usize) (row : Nat) :
    AspisV8.SelectedSelectorExpansion.tensorProduct
      (exactCoordinates (prefixSlice point).val) 6 row =
    AspisV8.SelectedSelectorExpansion.tensorProduct (exactPoint point) 6 row := by
  unfold AspisV8.SelectedSelectorExpansion.tensorProduct
  apply Finset.prod_congr rfl
  intro i hi
  have hii : i < 6 := Finset.mem_range.mp hi
  rw [prefix_exactCoordinates point i hii]

private theorem tensor_suffix (point : Array QM 10#usize) (row : Nat) :
    AspisV8.SelectedSelectorExpansion.tensorProduct
      (fun i => exactCoordinates (suffixSlice point).val i) 4 row =
    AspisV8.SelectedSelectorExpansion.tensorProduct
      (fun i => exactPoint point (6+i)) 4 row := by
  unfold AspisV8.SelectedSelectorExpansion.tensorProduct
  apply Finset.prod_congr rfl
  intro i hi
  have hii : i < 4 := Finset.mem_range.mp hi
  apply congrArg (fun x : ExactQM =>
    AspisV8.SelectedSelectorExpansion.factor x (row.testBit (4 - 1 - i)))
  exact suffix_exactCoordinates point i hii

/-- The actual generated `Selectors::at_point` succeeds from one canonical
10-cell point and its two outputs realize the corresponding 6/4 products. -/
theorem at_point_products (point : Array QM 10#usize)
    (hpoint : canonicalArray point) :
    ∃ selectors : pool_v1.pair_forest_copy_terminal.Selectors,
      pool_v1.pair_forest_copy_terminal.Selectors.at_point point = .ok selectors ∧
      canonicalArray selectors.high ∧ canonicalArray selectors.low ∧
      (∀ row : Fin 64,
        decodedArray selectors.high row.val =
          AspisV8.SelectedSelectorExpansion.tensorProduct (exactPoint point) 6 row.val) ∧
      (∀ row : Fin 16,
        decodedArray selectors.low row.val =
          AspisV8.SelectedSelectorExpansion.tensorProduct
            (fun i => exactPoint point (6+i)) 4 row.val) := by
  let pre := prefixSlice point
  let post := suffixSlice point
  have hpre : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice QM)) point
      ({ «end» := 6#usize } : core.ops.range.RangeTo Usize) = .ok pre := by
    simpa [pre] using prefix_read point
  have hpost : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeFromUsizeSlice QM)) point
      ({ start := 6#usize } : core.ops.range.RangeFrom Usize) = .ok post := by
    simpa [post] using suffix_read point
  obtain ⟨high, hhighRun, hhighCanon, hhighModel⟩ :=
    expand_model 64#usize pre
      (by
        have hmax : 4294967295 ≤ Usize.max := Usize.cMax_bound_concrete.1
        simp [pre, prefixSlice, point.property, List.slice_length])
      (prefix_coordinates_canonical point hpoint)
  obtain ⟨low, hlowRun, hlowCanon, hlowModel⟩ :=
    expand_model 16#usize post
      (by
        have hmax : 4294967295 ≤ Usize.max := Usize.cMax_bound_concrete.1
        simp [post, suffixSlice, point.property])
      (suffix_coordinates_canonical point hpoint)
  refine ⟨⟨high, low⟩, ?_, hhighCanon, hlowCanon, ?_, ?_⟩
  · unfold pool_v1.pair_forest_copy_terminal.Selectors.at_point
    simp only [hpre, bind_tc_ok, hhighRun, bind_tc_ok,
      hpost, bind_tc_ok, hlowRun, bind_tc_ok]
  · intro row
    have hrowN : row.val < (64#usize).val := by simpa using row.isLt
    have hrowPower : row.val < 2 ^ pre.val.length := by
      simpa [pre, prefixSlice, point.property, List.slice_length] using row.isLt
    calc
      decodedArray high row.val =
          expandListModel pre.val 0 (fun i => if i = 0 then 1 else 0) row.val :=
        hhighModel ⟨row.val, hrowN⟩
      _ = AspisV8.SelectedSelectorExpansion.tensorProduct
          (exactCoordinates pre.val) pre.val.length row.val :=
        generated_expand_product pre.val row.val hrowPower
      _ = AspisV8.SelectedSelectorExpansion.tensorProduct
          (exactPoint point) 6 row.val := by
        simpa [pre, prefixSlice, point.property, List.slice_length] using
          tensor_prefix point row.val
  · intro row
    have hrowN : row.val < (16#usize).val := by simpa using row.isLt
    have hrowPower : row.val < 2 ^ post.val.length := by
      simpa [post, suffixSlice, point.property] using row.isLt
    calc
      decodedArray low row.val =
          expandListModel post.val 0 (fun i => if i = 0 then 1 else 0) row.val :=
        hlowModel ⟨row.val, hrowN⟩
      _ = AspisV8.SelectedSelectorExpansion.tensorProduct
          (exactCoordinates post.val) post.val.length row.val :=
        generated_expand_product post.val row.val hrowPower
      _ = AspisV8.SelectedSelectorExpansion.tensorProduct
          (fun i => exactPoint point (6+i)) 4 row.val := by
        simpa [post, suffixSlice, point.property] using tensor_suffix point row.val

/-- `boxed_at_point` is the generated thin wrapper around the proved actual
`at_point`; no additional source precondition is introduced. -/
theorem boxed_at_point_products (point : Array QM 10#usize)
    (hpoint : canonicalArray point) :
    ∃ selectors : pool_v1.pair_forest_copy_terminal.Selectors,
      pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors ∧
      canonicalArray selectors.high ∧ canonicalArray selectors.low ∧
      (∀ row : Fin 64,
        decodedArray selectors.high row.val =
          AspisV8.SelectedSelectorExpansion.tensorProduct (exactPoint point) 6 row.val) ∧
      (∀ row : Fin 16,
        decodedArray selectors.low row.val =
          AspisV8.SelectedSelectorExpansion.tensorProduct
            (fun i => exactPoint point (6+i)) 4 row.val) := by
  obtain ⟨selectors, hr, hh, hl, hhm, hlm⟩ := at_point_products point hpoint
  refine ⟨selectors, ?_, hh, hl, hhm, hlm⟩
  simpa [pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point] using hr

#print axioms at_point_products
#print axioms boxed_at_point_products
end AspisR1.SelectorAtPointModel
