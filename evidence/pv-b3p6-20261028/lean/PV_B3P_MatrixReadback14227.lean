import PV_B3P_MatrixStore14227
import PV_B3P_Ordered227
namespace PV_B3P_Binding14227
open Aeneas Aeneas.Std Result
set_option autoImplicit false

def matrix_read14 (sums : Matrix14) (row column : Usize) : Result U64 := do
  let values ← Array.index_usize sums row
  Array.index_usize values column

theorem matrix_read_after_write14 (sums : Matrix14) (row column : Usize) (value : U64)
    (hr : row.val < 3) (hc : column.val < 3) :
    (do let next ← source_matrix_store14 sums row column value; matrix_read14 next row column) = .ok value := by
  rw [matrix_store_binding14 sums row column value hr hc]
  unfold model_matrix_store14
  rw [PV_B3P_SelectIndex227.index_value sums row hr]
  simp only [bind_tc_ok]
  let oldRow : Array U64 3#usize := sums.val[row.val]'(by have h := sums.property; scalar_tac)
  rw [PV_B3P_Ordered227.bind_assoc]
  change (do
    let nextRow ← Array.update oldRow column value
    let next ← Array.update sums row nextRow
    matrix_read14 next row column) = .ok value
  rw [PV_B3P_ArrayWrite227.update oldRow column hc]
  simp only [bind_tc_ok]
  rw [PV_B3P_ArrayWrite227.update sums row hr]
  simp only [bind_tc_ok,matrix_read14]
  rw [PV_B3P_SelectIndex227.index_value (Aeneas.Std.Array.set sums row (Aeneas.Std.Array.set oldRow column value)) row hr]
  simp only [PV_B3P_ArrayWrite227.restored_value sums row hr,bind_tc_ok]
  rw [PV_B3P_SelectIndex227.index_value (Aeneas.Std.Array.set oldRow column value) column hc]
  exact congrArg Result.ok (PV_B3P_ArrayWrite227.restored_value oldRow column hc value)
#print axioms matrix_read_after_write14
end PV_B3P_Binding14227
