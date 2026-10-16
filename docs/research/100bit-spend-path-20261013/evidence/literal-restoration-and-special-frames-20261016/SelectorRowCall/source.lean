import SelectorRowSemantic
import ExtractedMaskQM31Exact
import SelectedSelectorExpansionCore
import Mathlib.Data.Nat.Bitwise

/-! Checked execution of the exact generated `Selectors.row` method.  The
contract is limited to an in-range row and canonical high/low arrays. -/
set_option autoImplicit false
namespace AspisR1.SelectorRowCall

open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1.SelectorAtPointModel
open AspisR1.SelectorExpansionCorrectness
open AspisR1.ExtractedMaskTowerAdd
open AspisR1.ExtractedMaskQM31Exact

abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
abbrev QM := field.QM31
abbrev ExactQM := AspisR1.SelectorAtPointModel.ExactQM
abbrev CanonicalQM := AspisR1.SelectorAtPointModel.Canonical

def rowIndex (row : Usize) : Nat := row.val / 16
def columnIndex (row : Usize) : Nat := row.val % 16

private theorem array_index_usize_ok {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (hi : i.val < n.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

private theorem shift4_success (row : Usize) :
    ∃ i : Usize, row >>> 4#i32 = .ok i ∧ i.val = row.val / 16 := by
  have hy0 : 0 ≤ (4#i32).val := by norm_num
  have hy1 : (4#i32).val < UScalarTy.Usize.numBits := by
    cases System.Platform.numBits_eq <;>
      norm_num [UScalarTy.Usize_numBits_eq, *]
  have hspec := UScalar.ShiftRight_IScalar_spec row (4#i32) hy0 hy1
  obtain ⟨i, hrun, ⟨hval, _⟩⟩ := WP.spec_imp_exists hspec
  refine ⟨i, hrun, ?_⟩
  rw [hval]
  simp [IScalar.toNat, Nat.shiftRight_eq_div_pow]

private theorem mask15_success (row : Usize) :
    ∃ i : Usize, lift (row &&& 15#usize) = .ok i ∧ i.val = row.val % 16 := by
  obtain ⟨i, hrun, hspec⟩ := WP.spec_imp_exists (UScalar.and_spec row (15#usize))
  refine ⟨i, hrun, ?_⟩
  have h15 : (15#usize).val = 15 := by rfl
  have hval : (row &&& 15#usize).val = row.val % 16 := by
    rw [UScalar.val_and, h15]
    simpa only [show (16 : Nat) = 2 ^ 4 by norm_num] using
      (Nat.and_two_pow_sub_one_eq_mod row.val 4)
  exact hspec.1.trans hval

theorem row_success_of_canonical
    (selectors : Selectors) (row : Usize) (hrow : row.val < 1024)
    (hhigh : canonicalArray selectors.high) (hlow : canonicalArray selectors.low) :
    ∃ out : QM,
      pool_v1.pair_forest_copy_terminal.Selectors.row selectors row = .ok out ∧
      CanonicalQM out ∧
      AspisR1.ExtractedMaskQM31Exact.decode out =
        decodedArray selectors.high (row.val / 16) *
          decodedArray selectors.low (row.val % 16) := by
  obtain ⟨i, hi, hiv⟩ := shift4_success row
  obtain ⟨i1, hi1, hi1v⟩ := mask15_success row
  have hquot : row.val / 16 < 64 := by omega
  have hrem : row.val % 16 < 16 := Nat.mod_lt _ (by omega)
  have h64 : (64#usize).val = 64 := by scalar_tac
  have h16 : (16#usize).val = 16 := by scalar_tac
  have hiFinBound : i.val < 64 := by rw [hiv]; exact hquot
  have hi1FinBound : i1.val < 16 := by rw [hi1v]; exact hrem
  have hiBound : i.val < (64#usize).val := by rw [h64]; exact hiFinBound
  have hi1Bound : i1.val < (16#usize).val := by rw [h16]; exact hi1FinBound
  have hreadHigh : Array.index_usize selectors.high i =
      .ok (selectors.high.val[i.val]'(by simpa [selectors.high.property] using hiBound)) :=
    array_index_usize_ok selectors.high i hiBound
  have hreadLow : Array.index_usize selectors.low i1 =
      .ok (selectors.low.val[i1.val]'(by simpa [selectors.low.property] using hi1Bound)) :=
    array_index_usize_ok selectors.low i1 hi1Bound
  let x := selectors.high.val[i.val]'(by simpa [selectors.high.property] using hiBound)
  let y := selectors.low.val[i1.val]'(by simpa [selectors.low.property] using hi1Bound)
  have hx : CanonicalQM x := hhigh ⟨i.val, hiFinBound⟩
  have hy : CanonicalQM y := hlow ⟨i1.val, hi1FinBound⟩
  obtain ⟨out, hmul, hout, hdecode⟩ := current_qm_mul_exact x y hx hy
  refine ⟨out, ?_, hout, ?_⟩
  · unfold pool_v1.pair_forest_copy_terminal.Selectors.row
    simp only [hi, bind_tc_ok, hreadHigh, bind_tc_ok, hi1, bind_tc_ok,
      hreadLow, bind_tc_ok]
    change x.mul y = .ok out
    exact hmul
  · rw [hdecode]
    change AspisR1.ExtractedMaskQM31Exact.decode x * AspisR1.ExtractedMaskQM31Exact.decode y = _
    simp [x, y, decodedArray, decodedAt, hiv, hi1v, hquot, hrem,
      SelectorExpansionCorrectness.decode]

/-- Composition with the actual `boxed_at_point` output: the generated row
method succeeds, is canonical, and decodes to the ten-factor row weight. -/
theorem boxed_row_matches_ten_factor
    (point : Array QM 10#usize) (hpoint : canonicalArray point)
    (row : Usize) (hrow : row.val < 1024) :
    ∃ selectors : Selectors, ∃ out : QM,
      pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors ∧
      pool_v1.pair_forest_copy_terminal.Selectors.row selectors row = .ok out ∧ CanonicalQM out ∧
      AspisR1.ExtractedMaskQM31Exact.decode out = AspisV8.SelectedSelectorExpansion.tensorProduct
        (exactPoint point) 10 row.val := by
  obtain ⟨selectors, hbox, hhigh, hlow, hmodel⟩ :=
    AspisR1.SelectorRowSemantic.boxed_row_products point hpoint
  obtain ⟨out, hrun, hcanon, hdecode⟩ :=
    row_success_of_canonical selectors row hrow hhigh hlow
  refine ⟨selectors, out, hbox, hrun, hcanon, ?_⟩
  have ⟨hshift, hmask⟩ :=
    AspisV8.SelectedSelectorExpansion.selected_index_arithmetic row.val
  have hmodelRow := hmodel ⟨row.val, hrow⟩
  calc
    AspisR1.ExtractedMaskQM31Exact.decode out = decodedArray selectors.high (row.val / 16) *
        decodedArray selectors.low (row.val % 16) := hdecode
    _ = decodedArray selectors.high (row.val >>> 4) *
        decodedArray selectors.low (row.val &&& 15) := by rw [hshift, hmask]
    _ = AspisV8.SelectedSelectorExpansion.selectedSelector (exactPoint point) row.val := hmodelRow.1
    _ = AspisV8.SelectedSelectorExpansion.tensorProduct (exactPoint point) 10 row.val :=
      AspisV8.SelectedSelectorExpansion.selected_selector_product
        (exactPoint point) row.val hrow

#print axioms row_success_of_canonical
#print axioms boxed_row_matches_ten_factor
end AspisR1.SelectorRowCall
