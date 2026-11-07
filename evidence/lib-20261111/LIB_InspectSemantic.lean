import LIB_VCode
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let names := ["AspisR1.FJn_BeginCanonical.value","AspisR1PublicPreparation.ActualBeginSelectedCanonical.begin_challenges_selected_canonical","AspisR1.FIv_NativeValue.Canon","AspisR1PublicPreparation.S1SemanticCode.begin_erasure","AspisR1PublicPreparation.S1SemanticCode.publicTranscript_erasure","AspisR1PublicPreparation.S1SemanticCode.rounds_erasure"]
 for (n,c) in env.constants.toList do
  if names.contains n.toString then
   let owner := (env.getModuleIdxFor? n).map (fun idx=>env.header.moduleNames[idx]!)
   logInfo m!"{n}: {c.type}, OWNER {owner}"
#print AspisR1.NP6_StdModel.Reservation
#print AspisR1.NP6_StdModel.ReserveError
#print AspisR1ClaimsUnrolledParent.decodeRows
#print AspisR1.FIw_ArrayValue.canonical
#print AspisR1.FIv_NativeValue.Canon
