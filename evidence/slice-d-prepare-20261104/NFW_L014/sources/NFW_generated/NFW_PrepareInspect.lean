import NFQ_STAGE2_IMPORT
import NFS_QueryLoopRoot
#print AspisR1CurrentCaller.verifier.candidate.prepare
#print AspisR1CurrentCaller.OriginalPreparedSource.powers
#print AspisR1PublicPreparation.PreparedScratchModel.Boundaries
#print AspisR1LoopPowers.weights.early_powers
#print AspisR1LoopPowers.early_powers_total_exact
#print AspisR1LoopPowers.Canonical
#print AspisR1LoopPowers.decode
#print NEV_DotInputs.Canonical

open Lean Elab Command
run_cmd do
 for (n, ci) in (← getEnv).constants.toList do
  let s := n.toString
  if (s.contains "Powers" || s.contains "PowersExact") && (s.contains "inject" || s.endsWith "decode" || s.endsWith "decode_mul" || s.endsWith "canonical_inj") then
   logInfo m!"{n} : {ci.type}"
