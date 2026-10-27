import JGm_TX2_Level0_17
import JGm_TX2_Level1_17
import JGm_TX2_Level2_09
import JGm_TX2_ParentCalls0
import JGm_TX2_ParentCalls1
import JGm_TX2_ParentCalls2
import JGm_TX2_PaddingScan
import JGk_TX2_Partial
import JGc_TX2_Obstruction70
import ARX_Root
/- Mandatory 070 review. The actual BatchGoal is unchanged. None of these
local buffer-content/control results assumes successful slot/batch/finish or
accepted-wrapper execution. A computed batch result is still required. -/
#print AspisR1.JGc_TX2_Obstruction70.BatchGoal
#print AspisR1.JFn_HashBoundary.Realizes
#print axioms AspisR1.JGm_TX2_Level0_17.source
#print axioms AspisR1.JGm_TX2_Level1_17.source
#print axioms AspisR1.JGm_TX2_Level2_09.source
#print axioms AspisR1.JGm_TX2_PaddingScan.source
#print axioms AspisR1.JGk_TX2_Partial.local_nonvacuity
#print axioms AspisR1.ARX_Root.deployed
#check @AspisR1.ARX_Root.deployed
