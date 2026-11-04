import NFQ_STAGE2_IMPORT
import NFW_PowersDomain
#print AspisR1ClaimPreparedBridge.powersPublic
#print AspisR1.FIp_PowersValue.powers
#print AspisR1.FIp_PowersState.Post
#print AspisR1CurrentWide.Proof.decodeWide
#print AspisR1CurrentWide.Proof.decodeQM
#print AspisR1CurrentWide.Proof.decodeCM
#print AspisR1CurrentWide.Proof.decodeM31
open Lean Elab Command
run_cmd do
 let env ← getEnv
 for n in [`AspisR1.FIp_PowersValue.powers,`FIo_Native.weights.powers,`AspisR1LoopPowers.early_powers_total_exact] do
  match env.getModuleIdxFor? n with
  | some i => logInfo m!"OWNER {n} := {env.header.moduleNames[i.toNat]!}"
  | none => logInfo m!"MISSING {n}"
