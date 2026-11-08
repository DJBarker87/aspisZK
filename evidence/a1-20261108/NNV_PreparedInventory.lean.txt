import NNH_Run5bPreparedModel
import NNH_Run5bPreparedDigest
import LIB_Prepared
import NNH_ObservedReturns
set_option autoImplicit false
#print AspisR1CurrentCaller.S1SemanticCarrier.currentSem
#print AspisR1CurrentCaller.InstalledPreparation.retainedView
#print AspisR1CurrentCaller.InstalledPreparation.currentView
#print AspisR1CurrentCaller.InstalledPreparation.currentE
#print AspisR1CurrentCaller.InstalledPreparation.currentPrepared
#print AspisR1CurrentCaller.FirstComposition.toRetainedPublic
#print AspisR1PublicPreparation.VerifyPrefix.verify
#print NNH_FinishReturns.value
open Lean in
run_cmd do
 for (n,ci) in (← getEnv).constants.toList do
  let s := n.toString
  if ci.isTheorem && (s.startsWith "AspisR1CurrentCaller.InstalledPreparation." || s.startsWith "AspisR1CurrentCaller.S1SemanticCarrier.") &&
   (["round", "back", "map"].any (fun p => s.contains p)) then
   logInfo m!"{n}: {ci.type}"
