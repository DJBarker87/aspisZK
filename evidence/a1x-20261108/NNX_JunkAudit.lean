import NNV_DecodeP1880
import NNH_Tx1Returns
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNX_JunkAudit
open RSL
/-- The sole explicit Ok junk choice in the 345 evaluator is unreachable. -/
theorem wrong_accounts (a : TX1_345.Args) (env : Env)
 (bad : a.accounts.length ≠ 3) :
 NNH_ReturnsBundle.tx1Value a env = .error .invalidInstructionData := by
 have route : TX1_345.badRoute a = true := by simp [TX1_345.badRoute,bad]
 change NNH_Stage1RefEval.value _ _ _ _ a env = _
 simp only [NNH_Stage1RefEval.value,route,if_true]
/-- Reaching the non-route-error arm rules out every panic account pattern. -/
theorem route_length (a : TX1_345.Args) (route : TX1_345.badRoute a = false) :
 a.accounts.length = 3 := by
 by_contra bad
 have : TX1_345.badRoute a = true := by simp [TX1_345.badRoute,bad]
 rw [this] at route
 cases route
#print axioms wrong_accounts
#print axioms route_length
end AspisR1.NNX_JunkAudit
end
