import NNH_Run5bCurrentInventory
import NNH_Run5bPreparedModel
import LIBC_CanonicalScan
import LIBC_Prepared
set_option autoImplicit false
#print AspisR1.Uni_Install.current
#print NNH_Tx2Configuration.configuration
#print AspisR1CurrentCaller.InstalledPreparation.retainedSem
#print AspisR1CurrentCaller.S1SemanticInstallation.verify
#print AspisR1CurrentCaller.S1SemanticInstallation.install
#print AspisR1.IDa_Deployed.deployedConfiguration
#print AspisR1.Uni_Install.base
#print AspisR1CurrentCaller.S1SemanticCarrier.currentSem
open Lean in
run_cmd do
 for (n,ci) in (← getEnv).constants.toList do
  if ci.isTheorem && (["scan", "semantic", "Verified", "verified", "retainedSem"].any (fun p => n.toString.contains p)) &&
    (["AspisR1.NKL", "AspisR1CurrentCaller", "LIBC", "LIB_"].any (fun p => n.toString.startsWith p)) then
   logInfo m!"{n}: {ci.type}"
