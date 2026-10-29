import PV_B3P_ExpandSuccess227
import PV_B3P_P227_12
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

theorem usize_1024_size : 1024 < UScalar.size .Usize := by
  have hm := Usize.cMax_bound_concrete.1
  rw [UScalar.size_def]
  scalar_tac

/-- Small symbolic layout constant, not a recurrence evaluation. -/
theorem selected_columns28 :
    reference_terminal.POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1 = .ok 28#usize := by
  unfold reference_terminal.POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1
    reference_terminal.POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1
    aspis_core.state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS
  rfl

theorem selected_claim_total (claims : Array aspis_core.field.QM31 84#usize)
    (row column : Usize) (hr : row.val<3) (hc : column.val<28) :
    Success (reference_terminal.selected_claim claims row column) := by
  let j := Usize.wrapping_mul row 28#usize
  have hj : j.val = row.val*28 := by
    have h := usize_mul_value row 28#usize (by have hsize := usize_1024_size; change row.val*28 < _; omega)
    simpa only [show (28#usize).val=28 from rfl] using h
  let k := Usize.wrapping_add j column
  have hk : k.val=j.val+column.val :=
    PV_B3P_Offset226V3.add_value j column (by have hsize := usize_1024_size; omega)
  obtain ⟨value,hvalue⟩ := index claims k (by change k.val<84; omega)
  unfold reference_terminal.selected_claim
  rw [selected_columns28]
  simp only [lift,bind_tc_ok]
  exact ⟨value,hvalue⟩

#print axioms usize_1024_size
#print axioms selected_columns28
#print axioms selected_claim_total
end PV_B3P_Success227
