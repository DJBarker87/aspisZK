import FJc_S2Rows
set_option autoImplicit false
namespace AspisR1.FJc_MaskTable0
/-- Static S2 mask correspondence for one bounded block; each closed cell
uses only tiny integer bit arithmetic and fixed table lookup, no recurrence. -/
theorem value (j s : Nat) (lo : 0≤j) (hi : j<16) (hs : s<16) :
    FJc_S2Rows.selected j s ↔ FJc_S2Rows.inactive j s := by
  interval_cases j <;> interval_cases s <;> decide
#print axioms value
end AspisR1.FJc_MaskTable0
