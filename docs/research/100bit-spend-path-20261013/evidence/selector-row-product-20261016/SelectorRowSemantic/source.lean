import SelectorAtPointModel
import SelectedSelectorExpansionCore

/-! Rowwise composition of the checked 6+4 selector outputs with the old
selected-selector product identity. This is a model relation over the exact
coordinates decoded from the actual point input. -/
set_option autoImplicit false
namespace AspisR1.SelectorRowSemantic

open Aeneas.Std
open AspisR1SelectedMaskProbe
open AspisR1.SelectorAtPointModel
open AspisR1.SelectorExpansionCorrectness

/-- The actual boxed selector outputs give the old 10-coordinate selected
product at every in-range row, and hence its 10-factor row weight. -/
theorem boxed_row_products (point : Array (AspisR1.SelectorAtPointModel.QM) 10#usize)
    (hpoint : canonicalArray point) :
    ∃ selectors : pool_v1.pair_forest_copy_terminal.Selectors,
      pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors ∧
      canonicalArray selectors.high ∧ canonicalArray selectors.low ∧
      ∀ row : Fin 1024,
        (decodedArray selectors.high (row.val >>> 4) *
          decodedArray selectors.low (row.val &&& 15) =
          AspisV8.SelectedSelectorExpansion.selectedSelector
            (exactPoint point) row.val) ∧
        (decodedArray selectors.high (row.val >>> 4) *
          decodedArray selectors.low (row.val &&& 15) =
          AspisV8.SelectedSelectorExpansion.tensorProduct (exactPoint point) 10 row.val) := by
  obtain ⟨selectors, hrun, hhighCanon, hlowCanon, hhigh, hlow⟩ :=
    boxed_at_point_products point hpoint
  refine ⟨selectors, hrun, hhighCanon, hlowCanon, ?_⟩
  intro row
  let n := row.val
  have hn : n < 1024 := row.isLt
  have hhighN : n / 16 < 64 := by omega
  have hlowN : n % 16 < 16 := Nat.mod_lt _ (by omega)
  have hhighPow : n / 16 < 2 ^ 6 := by
    simpa only [show (2 ^ 6 : Nat) = 64 by norm_num] using hhighN
  have hlowPow : n % 16 < 2 ^ 4 := by
    simpa only [show (2 ^ 4 : Nat) = 16 by norm_num] using hlowN
  have ⟨hshift, hmask⟩ :=
    AspisV8.SelectedSelectorExpansion.selected_index_arithmetic n
  have hhighTensor :
      decodedArray selectors.high (n / 16) =
        AspisV8.SelectedSelectorExpansion.tensorProduct (exactPoint point) 6 (n / 16) :=
    hhigh ⟨n / 16, by simpa using hhighN⟩
  have hlowTensor :
      decodedArray selectors.low (n % 16) =
        AspisV8.SelectedSelectorExpansion.tensorProduct
          (fun i => exactPoint point (6+i)) 4 (n % 16) :=
    hlow ⟨n % 16, by simpa using hlowN⟩
  have hselected :
      decodedArray selectors.high (n >>> 4) * decodedArray selectors.low (n &&& 15) =
        AspisV8.SelectedSelectorExpansion.selectedSelector (exactPoint point) n := by
    calc
      decodedArray selectors.high (n >>> 4) * decodedArray selectors.low (n &&& 15) =
          AspisV8.SelectedSelectorExpansion.tensorProduct (exactPoint point) 6 (n / 16) *
            AspisV8.SelectedSelectorExpansion.tensorProduct
              (fun i => exactPoint point (6+i)) 4 (n % 16) := by
            rw [hshift, hmask, hhighTensor, hlowTensor]
      _ = AspisV8.SelectedSelectorExpansion.selectedSelector (exactPoint point) n := by
        unfold AspisV8.SelectedSelectorExpansion.selectedSelector
        rw [hshift, hmask]
        have hhighExpand := AspisV8.SelectedSelectorExpansion.expand_product
          (exactPoint point) 6 (n / 16) hhighPow
        have hlowExpand := AspisV8.SelectedSelectorExpansion.expand_product
          (fun i => exactPoint point (6+i)) 4 (n % 16) hlowPow
        rw [← hhighExpand, ← hlowExpand]
  refine ⟨?_, ?_⟩
  · simpa [n] using hselected
  · calc
      decodedArray selectors.high (row.val >>> 4) * decodedArray selectors.low (row.val &&& 15) =
          AspisV8.SelectedSelectorExpansion.selectedSelector (exactPoint point) row.val := by
        simpa [n] using hselected
      _ = AspisV8.SelectedSelectorExpansion.tensorProduct (exactPoint point) 10 row.val :=
        AspisV8.SelectedSelectorExpansion.selected_selector_product
          (exactPoint point) row.val row.isLt

#print axioms boxed_row_products
end AspisR1.SelectorRowSemantic
