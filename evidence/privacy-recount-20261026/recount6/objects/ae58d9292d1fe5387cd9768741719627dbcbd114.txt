import R1Z.PV_B2_RawWeights253Funs
set_option autoImplicit false
namespace PV_B2_ErrorCounterexample
open Aeneas Aeneas.Std Result
open PV_B2_253b10

/-- The new copied D row guard changes the failure constructor. -/
theorem copied_row_failure :
    host_weights.host_row .D 1024#usize = fail .assertionFailure := by
  have h : ¬ (1024#usize < 1024#usize) := by decide
  simp only [host_weights.host_row,massert,if_neg h,bind_tc_fail]

/-- This is the frozen source's array-read operation, independent of table data. -/
theorem original_index_failure (table : Array U16 1024#usize) :
    Array.index_usize table 1024#usize = fail .arrayOutOfBounds := by
  simp only [Array.index_usize,Array.getElem?_Usize_eq]
  rw [List.getElem?_eq_none (by simpa only [table.property] using Nat.le_refl (1024#usize).val)]

/-- Every continuation of the frozen D table read preserves its bounds failure. -/
theorem original_prefix_failure {α : Type} (table : Array U16 1024#usize)
    (k : U16 → Result α) :
    (Array.index_usize table 1024#usize >>= k) = fail .arrayOutOfBounds := by
  simp only [original_index_failure,bind_tc_fail]

/-- The requested op253 root propagates the copied assertion failure. -/
theorem copied_raw_failure (w : host_weights.Weights) (hw : w.variant = .D) :
    pv_b2_raw w 0#usize 1024#usize = fail .assertionFailure := by
  simp only [pv_b2_raw,host_weights.Weights.raw,host_weights.raw_value,
    ite_true,hw,copied_row_failure,bind_tc_fail]

/-- Counterexample to universal copy/original complete-Result equality:
D, kind0, index1024. The frozen source reads COEFFICIENT_TO_ROW[j] before
executing its continuation, so this result covers its actual constant table
and every subsequent computation. No original table contents are assumed. -/
theorem op253_copy_error_counterexample (w : host_weights.Weights)
    (hw : w.variant = .D) (table : Array U16 1024#usize)
    (k : U16 → Result aspis_core.field.QM31) :
    pv_b2_raw w 0#usize 1024#usize ≠ (Array.index_usize table 1024#usize >>= k) := by
  rw [copied_raw_failure w hw,original_prefix_failure]
  intro h
  cases h

#print axioms copied_row_failure
#print axioms original_index_failure
#print axioms original_prefix_failure
#print axioms copied_raw_failure
#print axioms op253_copy_error_counterexample
end PV_B2_ErrorCounterexample
