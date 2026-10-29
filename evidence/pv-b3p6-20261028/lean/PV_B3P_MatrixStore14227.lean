import PV_B3P_ArrayWrite227
namespace PV_B3P_Binding14227
open Aeneas Aeneas.Std Result
set_option autoImplicit false
abbrev Matrix14 := Array (Array U64 3#usize) 3#usize

def source_matrix_store14 (sums : Matrix14) (row column : Usize) (value : U64) : Result Matrix14 := do
  let (old_row,back_matrix) ← Array.index_mut_usize sums row
  let (_old,back_row) ← Array.index_mut_usize old_row column
  .ok (back_matrix (back_row value))

def model_matrix_store14 (sums : Matrix14) (row column : Usize) (value : U64) : Result Matrix14 := do
  let old_row ← Array.index_usize sums row
  let next_row ← Array.update old_row column value
  Array.update sums row next_row

def PV_B3P_Link_matrix_stores
    (native : Matrix14 → Usize → Usize → U64 → Result Matrix14) : Prop :=
  ∀ sums row column value, row.val < 3 → column.val < 3 →
    native sums row column value = model_matrix_store14 sums row column value

theorem matrix_store_binding14 (sums : Matrix14) (row column : Usize) (value : U64)
    (hr : row.val < 3) (hc : column.val < 3) :
    source_matrix_store14 sums row column value = model_matrix_store14 sums row column value := by
  unfold source_matrix_store14 model_matrix_store14
  rw [PV_B3P_ArrayWrite227.borrow sums row hr,PV_B3P_SelectIndex227.index_value sums row hr]
  simp only [bind_tc_ok]
  let rowValue : Array U64 3#usize := sums.val[row.val]'(by have h := sums.property; scalar_tac)
  change (do
    let (_old,back_row) ← Array.index_mut_usize rowValue column
    .ok (Aeneas.Std.Array.set sums row (back_row value))) = (do
    let next_row ← Array.update rowValue column value
    Array.update sums row next_row)
  rw [PV_B3P_ArrayWrite227.borrow rowValue column hc,
      PV_B3P_ArrayWrite227.update rowValue column hc]
  simp only [bind_tc_ok]
  exact (PV_B3P_ArrayWrite227.update sums row hr (Aeneas.Std.Array.set rowValue column value)).symm

theorem matrix_stores_link14 : PV_B3P_Link_matrix_stores source_matrix_store14 :=
  matrix_store_binding14
#print axioms matrix_store_binding14
#print axioms matrix_stores_link14
end PV_B3P_Binding14227
