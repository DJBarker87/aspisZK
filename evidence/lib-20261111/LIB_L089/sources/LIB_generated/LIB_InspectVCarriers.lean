import LIB_Carriers
import LIB_ErrorDebug
import NJM_InvocationRoots
import NKA_ClaimsRoot
import NLH_WrapperRoot
import NHU_Mask
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let names := ["AspisR1PublicPreparation.r1_wire.Prefix.mk",
  "AspisR1PublicPreparation.r1_wire.Challenges.mk",
  "AspisR1PublicPreparation.r1_wire.ValidatedRecord.mk",
  "AspisR1PublicPreparation.r1_wire.SemanticTranscript.mk",
  "AspisR1PublicPreparation.aspis_core.circle.SecureCirclePoint.mk",
  "AspisR1PublicPreparation.aspis_core.field.QM31.mk",
  "AspisR1PublicPreparation.verifier.Prepared.mk","AspisR1PublicPreparation.verifier.View.mk",
  "AspisR1PublicPreparation.verifier.Accumulator.mk","AspisR1PublicPreparation.verifier.QueryGeometry.mk",
  "AspisR1PublicPreparation.verifier.BatchedWeights.mk","AspisR1PublicPreparation.r1_wire.Challenges.eta",
  "AspisR1PublicPreparation.aspis_core.r0.Challenges.mk","VTop_Stages.verifier.Prepared.mk","VTop_Stages.verifier.View.mk",
  "VTop_Stages.verifier.Accumulator.mk","VTop_Stages.verifier.QueryGeometry.mk",
  "VTop_Stages.verifier.BatchedWeights.mk","VTop_Stages.compact.CodecError",
  "AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public","AspisR1.LPi_FieldValues.canonQ","LPi_FieldValues.canonQ"]
 for (n,c) in env.constants.toList do
  if names.contains n.toString || n.toString.endsWith ".QueryGeometry.mk" ||
     n.toString.endsWith ".BatchedWeights.mk" || n.toString.endsWith ".Challenges.mk" then
   let owner := (env.getModuleIdxFor? n).map (fun idx => env.header.moduleNames[idx]!)
   logInfo m!"{n} : {c.type}; owner={owner}"
