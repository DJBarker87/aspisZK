import NGK_COMBINED_IMPORT
import NIU_COMBINED_IMPORT
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for root in #["AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.generated_m31_mul_eq_probe",
    "AspisR1SelectedMaskProbe.field.M31.reduce_u62",
    "AspisR1.RawPoseidonExtensionWords.current_reduce_u62_mod",
    "AspisR1.RawPoseidonExternalRows.rawRowNat",
    "AspisR1.RawPoseidonExternalRows.rowFormula_eq_poseidonMat4",
    "AspisR1.ExtractedMaskReducer.current_mul_mod"] do
    if let some idx := env.getModuleIdxFor? root.toName then
      logInfo m!"NJA_OWNER {root} {env.header.moduleNames[idx]!}"
    else logInfo m!"NJA_OWNER_MISSING {root}"
