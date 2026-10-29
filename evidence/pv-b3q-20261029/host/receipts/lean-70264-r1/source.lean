import PV_B3Q_MatrixTrace
namespace PV_B3Q_MatrixFrame
open Aeneas Aeneas.Std PV_B3P_Binding14227 PV_B3Q_Matrix
set_option autoImplicit false

theorem read_set_same {α : Type} {n : Usize} (xs : Array α n) (index : Usize)
    (value : α) (bound : index.val<n.val) :
    Array.index_usize (Aeneas.Std.Array.set xs index value) index = .ok value := by
 rw [PV_B3P_SelectIndex227.index_value _ index bound]
 exact congrArg Result.ok (PV_B3P_ArrayWrite227.restored_value xs index bound value)
theorem read_set_other {α : Type} {n : Usize} (xs : Array α n) (index other : Usize)
    (value : α) (bound : index.val<n.val) (other_bound : other.val<n.val)
    (different : index.val≠other.val) :
    Array.index_usize (Aeneas.Std.Array.set xs index value) other = Array.index_usize xs other := by
 rw [PV_B3P_SelectIndex227.index_value _ other other_bound,
     PV_B3P_SelectIndex227.index_value xs other other_bound]
 exact congrArg Result.ok (PV_B3P_ArrayWrite227.restored_frame xs index other bound other_bound different value)
def row_at (sums : Matrix14) (row : Usize) (bound : row.val<3) : Array U64 3#usize :=
 sums.val[row.val]'(by have length := sums.property; scalar_tac)
theorem complete_store (sums : Matrix14) (row column : Usize) (value : U64)
    (hr : row.val<3) (hc : column.val<3) :
    deployed_store sums row column value = .ok
      (Aeneas.Std.Array.set sums row (Aeneas.Std.Array.set (row_at sums row hr) column value)) := by
 unfold deployed_store
 rw [PV_B3P_ArrayWrite227.borrow sums row hr]
 simp only [bind_tc_ok]
 change (do
   let (_,back) ← Array.index_mut_usize (row_at sums row hr) column
   .ok (Aeneas.Std.Array.set sums row (back value))) = _
 rw [PV_B3P_ArrayWrite227.borrow (row_at sums row hr) column hc]
 rfl
/-- Every untouched row is retained in full, not just one observed word. -/
theorem other_row (sums : Matrix14) (row column other : Usize) (value : U64)
    (hr : row.val<3) (hc : column.val<3) (ho : other.val<3) (different : row.val≠other.val) :
    (do let next ← deployed_store sums row column value; Array.index_usize next other) =
      Array.index_usize sums other := by
 rw [complete_store sums row column value hr hc]
 simp only [bind_tc_ok]
 exact read_set_other sums row other _ hr ho different
/-- Every untouched channel of the changed row is retained. Together with the
readback law this accounts for every one of the nine observed entries. -/
theorem other_channel (sums : Matrix14) (row column other : Usize) (value : U64)
    (hr : row.val<3) (hc : column.val<3) (ho : other.val<3) (different : column.val≠other.val) :
    (do let next ← deployed_store sums row column value; matrix_read14 next row other) =
      matrix_read14 sums row other := by
 rw [complete_store sums row column value hr hc]
 simp only [bind_tc_ok,matrix_read14]
 rw [read_set_same sums row _ hr,PV_B3P_SelectIndex227.index_value sums row hr]
 simp only [bind_tc_ok]
 exact read_set_other (row_at sums row hr) column other value hc ho different
/-- Existing storage link together with complete frame and target-read laws. -/
theorem link_and_target : PV_B3P_Link_matrix_stores deployed_store ∧
    ∀ sums row column value, row.val<3 → column.val<3 →
      (do let next ← deployed_store sums row column value; matrix_read14 next row column) = .ok value := by
 refine ⟨deployed_store_link,?_⟩
 intro sums row column value hr hc
 exact matrix_read_after_write14 sums row column value hr hc
#print axioms read_set_same
#print axioms read_set_other
#print axioms complete_store
#print axioms other_row
#print axioms other_channel
#print axioms link_and_target
end PV_B3Q_MatrixFrame
