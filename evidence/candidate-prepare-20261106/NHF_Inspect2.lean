import NGK_COMBINED_IMPORT
import NFW_PreparedProducer
open Lean Elab Command
run_cmd do
 for (n,ci) in (←getEnv).constants.toList do
  let s:=n.toString
  if (s.contains "WideModel" && s.endsWith "result") || (s.contains "WideView" && (s.endsWith "source" || s.endsWith "result" || s.endsWith "from_le_bytes")) then
   logInfo m!"{n} : {ci.type}"
#print AspisR1SelectedWideViewV1.viewFromBytes
#print AspisR1SelectedWideViewV1.compact.OFF_INACTIVE
#print AspisR1CurrentCaller.Ops.op5
#print AspisR1CurrentCaller.Ops.op6
#print AspisR1CurrentCaller.Ops.op9
