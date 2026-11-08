import NNH_Run5bCurrentInventory
import NNH_Run5bPreparedModel
import LIBC_CanonicalScan
import LIBC_Prepared
set_option autoImplicit false
#print AspisR1.Uni_Install.current
#print AspisR1.NNH_Tx2Configuration.configuration
#print NNH_Tx2Configuration.configuration
#print AspisR1CurrentCaller.InstalledPreparation.retainedSem
#print AspisR1CurrentCaller.S1SemanticInstallation.verify
#print AspisR1CurrentCaller.S1SemanticInstallation.install
#print LIBC_VPrepare.prepared
open Lean in
run_cmd do
 for (n,ci) in (← getEnv).constants.toList do
  if ci.isTheorem && (["scan", "semantic", "Verified", "verified", "retainedSem"].any n.toString.contains) &&
    (["AspisR1.NKL", "AspisR1CurrentCaller", "LIBC", "LIB_"].any n.toString.startsWith) then
   logInfo m!"{n}: {ci.type}"
