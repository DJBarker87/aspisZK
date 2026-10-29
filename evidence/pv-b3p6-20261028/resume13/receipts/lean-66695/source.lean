import PV_B3P_ArrayWrite227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std Result
set_option autoImplicit false
abbrev Matrix13 := Array (Array U64 3#usize) 3#usize

def source_matrix_store13 (sums : Matrix13) (row column : Usize) (value : U64) : Result Matrix13 := do
  let (old_row,back_matrix) ← Array.index_mut_usize sums row
  let (_old,back_row) ← Array.index_mut_usize old_row column
  .ok (back_matrix (back_row value))

def model_matrix_store13 (sums : Matrix13) (row column : Usize) (value : U64) : Result Matrix13 := do
  let old_row ← Array.index_usize sums row
  let next_row ← Array.update old_row column value
  Array.update sums row next_row

def PV_B3P_Link_matrix_stores
    (native : Matrix13 → Usize → Usize → U64 → Result Matrix13) : Prop :=
  ∀ sums row column value, row.val < 3 → column.val < 3 →
    native sums row column value = model_matrix_store13 sums row column value

theorem matrix_store_binding13 (sums : Matrix13) (row column : Usize) (value : U64)
    (hr : row.val < 3) (hc : column.val < 3) :
    source_matrix_store13 sums row column value = model_matrix_store13 sums row column value := by
  unfold source_matrix_store13 model_matrix_store13
  rw [PV_B3P_ArrayWrite227.borrow sums row hr,PV_B3P_SelectIndex227.index_value sums row hr]
  simp only [bind_tc_ok]
  dsimp only
  rw [PV_B3P_ArrayWrite227.borrow _ column hc,PV_B3P_ArrayWrite227.update _ column hc]
  simp only [bind_tc_ok]
  dsimp only
  rw [PV_B3P_ArrayWrite227.update _ row hr]

theorem matrix_stores_link13 : PV_B3P_Link_matrix_stores source_matrix_store13 :=
  matrix_store_binding13
#print axioms matrix_store_binding13
#print axioms matrix_stores_link13
end PV_B3P_Binding13227
