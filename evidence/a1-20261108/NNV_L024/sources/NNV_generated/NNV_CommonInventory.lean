import NNH_Run5bHost
import NNH_S1CodecOk
set_option autoImplicit false
#print NMT_345.commonValue
#print NMT_345Dec.fromT5
#print NMT_345Dec.toT5
#print NMT_345Dec.fromT7
#print AspisR1.S6N_Getters.commonValue
open Lean in
run_cmd do
 for (n,ci) in (← getEnv).constants.toList do
  let s := n.toString
  if s.startsWith "AspisS6CurrentAdapterCarrier." &&
    (["Common", "Afterstate", "Transition"].any (fun p => s.contains p)) then
   logInfo m!"{n}: {ci.type}"
