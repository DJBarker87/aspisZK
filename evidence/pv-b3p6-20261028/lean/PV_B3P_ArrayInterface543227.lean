import PV_B3P_ArrayWrite227
import PV_B3P_Offset226V3
namespace PV_B3P_Association543227
open Aeneas Aeneas.Std Result
set_option autoImplicit false

/-- Direct indexed assignment retains and applies the mutable loan's back function. -/
def source_store543 {α : Type} {n : Usize} (xs : Array α n) (i : Usize) (value : α) : Result (Array α n) := do
  let (_,back) ← Array.index_mut_usize xs i
  .ok (back value)

theorem source_store_update543 {α : Type} {n : Usize} (xs : Array α n) (i : Usize)
    (value : α) (bound : i.val < n.val) :
    source_store543 xs i value = Array.update xs i value := by
  unfold source_store543
  rw [PV_B3P_ArrayWrite227.borrow xs i bound,PV_B3P_ArrayWrite227.update xs i bound]
  rfl

theorem source_store_continuation543 {α β : Type} {n : Usize}
    (xs : Array α n) (i : Usize) (value : α) (bound : i.val < n.val)
    (next : Array α n → Result β) :
    (do let restored ← source_store543 xs i value; next restored) =
      (do let restored ← Array.update xs i value; next restored) := by
  rw [source_store_update543 xs i value bound]

/-- All occupancy accesses and stores, including the final fixed cell, fit
without a field-value or canonicality premise. -/
theorem occupancy_indices543 (lane : Usize) (bound : lane.val < 8) :
    (Usize.wrapping_add 2#usize lane).val < 16 ∧
    (Usize.wrapping_add 3#usize lane).val < 12 := by
  have size_bound : 16 < UScalar.size .Usize := by
    simpa only [UScalar.size] using (16#usize).hBounds
  have h2 := PV_B3P_Offset226V3.add_value 2#usize lane (by change 2 + lane.val < _; omega)
  have h3 := PV_B3P_Offset226V3.add_value 3#usize lane (by change 3 + lane.val < _; omega)
  constructor <;> scalar_tac

#print axioms source_store_update543
#print axioms source_store_continuation543
#print axioms occupancy_indices543
end PV_B3P_Association543227
