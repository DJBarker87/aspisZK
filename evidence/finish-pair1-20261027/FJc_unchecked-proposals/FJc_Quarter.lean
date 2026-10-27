import FJc_LowModel
import R1RoundPairing
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_Quarter
open AspisR1CurrentWide.Proof
/-- Symbolic modular identity for the installed quarter constant. -/
theorem inverse_four : (4 : ZMod 2147483647)*decodeM FIo_Native.weights.QUARTER=1 := by
  unfold FIo_Native.weights.QUARTER
  change (4 : ZMod 2147483647)*(536870912 : ZMod 2147483647)=1
  norm_num

theorem value : decodeM FIo_Native.weights.QUARTER=RoundPairing.quarter (K:=ZMod 2147483647) := by
  unfold RoundPairing.quarter
  apply mul_left_cancel₀ (show (4 : ZMod 2147483647)≠0 from by norm_num)
  rw [inverse_four,mul_inv_cancel₀ (show (4 : ZMod 2147483647)≠0 from by norm_num)]
#print axioms inverse_four
#print axioms value
end AspisR1.FJc_Quarter
end
