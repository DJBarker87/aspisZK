import FJc_S2Rows
set_option autoImplicit false
namespace AspisR1.FJc_MaskTable2
/-- Static S2 mask correspondence for one bounded block; each closed cell
uses only tiny integer bit arithmetic and fixed table lookup, no recurrence. -/
theorem value (j s : Nat) (lo : 32≤j) (hi : j<48) (hs : s<16) :
    FJc_S2Rows.selected j s ↔ FJc_S2Rows.inactive j s := by
  interval_cases j <;> interval_cases s <;>
    (unfold FJc_S2Rows.selected FJc_S2Rows.inactive FJc_S2Rows.activeMask FJc_S2Rows.row
      FJc_SubsetModel.mask FJc_GroupTable.group FIo_Native.weights.S2_INACTIVE_MASKS
      FIo_Native.weights.S2_INACTIVE_GROUPS FIo_Native.aspis_core.r0.opening.COPY_ACTIVE_ROW_MASKS
      Aeneas.Std.Array.make; decide)
#print axioms value
end AspisR1.FJc_MaskTable2
