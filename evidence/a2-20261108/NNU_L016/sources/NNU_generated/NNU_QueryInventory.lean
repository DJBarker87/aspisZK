import NNH_Run5bQueryDomain
import NNH_Run5bQuerySlots
import NFS_QueryLoopRoot
import Lean
set_option autoImplicit false
#check AspisR1.NFS_QueryLoopRoot.tx2
#check AspisR1.NFS_QueryInvariant.step
#check AspisR1.NFS_QueryValuesPacket.result
#print NBF_RowInstall.install
#print NBF_BasisInstall.install
#print AspisR1.SAQ_WideABI.toQ
#print AspisR1.SAQ_WideABI.fromQ
#print NBO_FieldPorts.toQ
#print NBO_FieldPorts.fromQ
run_cmd do
 let env ← Lean.getEnv
 for (n,i) in env.constants.toList do
  let s:=n.toString
  if i.isTheorem && ((s.startsWith "AspisR1CurrentWide." &&
   (s.contains "probe" || s.contains "total" || s.contains "inject")) ||
   (s.startsWith "JFv_RawExtractedSemanticCallOpsV20." && s.contains "mul_eq") ||
   (s.startsWith "AspisR1.SAQ_" && s.contains "probe")) then
   Lean.logInfo m!"{n}: {i.type}"
