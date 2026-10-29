import PV_B3P_MatrixStore14227
import PV_B3P_MatrixReadback14227
namespace PV_B3Q_Matrix
open Aeneas Aeneas.Std PV_B3P_Binding14227
set_option autoImplicit false
/-- The store of the deployed compound assignment, after its wrapping arithmetic.
The old scalar is deliberately discarded; both restoration functions are used. -/
def deployed_store (sums : Matrix14) (row column : Usize) (value : U64) : Result Matrix14 := do
  let (borrowed_row, restore_matrix) ← Array.index_mut_usize sums row
  let (_, restore_row) ← Array.index_mut_usize borrowed_row column
  let restored_row := restore_row value
  .ok (restore_matrix restored_row)
theorem deployed_store_link : PV_B3P_Link_matrix_stores deployed_store := by
  exact matrix_stores_link14
#print axioms deployed_store_link
end PV_B3Q_Matrix
