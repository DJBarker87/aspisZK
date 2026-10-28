import PV_B3_MaskSparse00
namespace PV_B3_MaskSparseCopy
open Aeneas Aeneas.Std Result PV_B3_Forest_134 PV_B3_MaskSparseStates
set_option autoImplicit false

-- Complete Result equation for the actual emitted copy root. The proof
-- consumes named local transitions; it never normalizes a whole run.
theorem source_result :
    host_forest.pool_v1_pair_forest_copy_active_row_masks_v1 =
      ok (.Ok (PV_B3_SparseArray.array 64#usize M136)) := by
  unfold host_forest.pool_v1_pair_forest_copy_active_row_masks_v1
  simp only [← PV_B3_SparseArray.constant 1024#usize 0#u8,
    ← PV_B3_SparseArray.constant 64#usize 0#u16]
  change run s000 = _
  exact PV_B3_MaskSparse00.suffix

theorem nonvacuity : ∃ masks : Array U16 64#usize,
    host_forest.pool_v1_pair_forest_copy_active_row_masks_v1 = ok (.Ok masks) ∧
      masks.val.length = 64 := by
  exact ⟨_, source_result, (PV_B3_SparseArray.array 64#usize M136).property⟩

#print axioms source_result
#print axioms nonvacuity
end PV_B3_MaskSparseCopy
