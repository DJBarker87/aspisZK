import RSL_TX2_217
set_option autoImplicit false
namespace NMX_R3_Extent
open RSL
/-- Extent is obtained from the first guard, never supplied by a row caller. -/
theorem canonical (b : Bytes) (passed : TX2_217.headerBad b = false) :
    b.length = LANE_ACCOUNT_BYTES := by
  by_contra wrong
  have bad : TX2_217.headerBad b = true := by
    simp only [TX2_217.headerBad,
      show (b.length != LANE_ACCOUNT_BYTES) = true by simp [wrong], Bool.true_or]
  rw [bad] at passed
  cases passed
#print axioms canonical
end NMX_R3_Extent
