import RPu_FJc_MaskTable0
import RPu_FJc_MaskTable1
import RPu_FJc_MaskTable2
import RPu_FJc_MaskTable3
set_option autoImplicit false
namespace AspisR1.FJc_MaskTable
/-- All1024 small static table cells, split by bounded coefficient blocks.
The target is the arithmetic S2 row; native row_loop/model joins stay separate. -/
theorem value (j s : Nat) (hj : j<64) (hs : s<16) :
    FJc_S2Rows.selected j s ↔ FJc_S2Rows.inactive j s := by
  by_cases h0 : j<16
  · exact FJc_MaskTable0.value j s (Nat.zero_le _) h0 hs
  by_cases h1 : j<32
  · exact FJc_MaskTable1.value j s (by omega) h1 hs
  by_cases h2 : j<48
  · exact FJc_MaskTable2.value j s (by omega) h2 hs
  · exact FJc_MaskTable3.value j s (by omega) hj hs
#print axioms value
end AspisR1.FJc_MaskTable
