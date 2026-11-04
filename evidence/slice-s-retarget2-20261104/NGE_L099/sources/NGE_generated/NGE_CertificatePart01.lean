import Lean
import NGE_COMBINED_IMPORT
open Lean
run_cmd do
 let env ← getEnv
 for n in (#[`NEX_AfterDecodeOracle.result_state_effects,`NEX_FirstError.at_error,`NEX_TerminalDomain.wrong_length,`NEY_Field12.alignment,`NEY_Field25.alignment,`NFY_NED_PaymentCohorts.canonical_result,`NFY_NEE_M31SerializerDomain.width,`NFY_NEM_SnapshotBorrow.poststate,`NFY_NEQ_PaymentDecode.withdrawal_substitution,`NFY_NEU_CallDomains.withdrawal_reply_range,`NFY_NEY_EmitComposed.encoder_bridge,`NFY_NFD_CommonField09.alignment,`NFY_NFD_EmitProjection.alignment7,`NFY_NFD_RequestField05.alignment,`NFY_NFD_RequestProjection.withdrawal_roundtrip,`NGE_NEJ_CommonSourceFrame.result_and_frame,`NGE_NEL_PaymentOracle.withdrawal_substitution,`NGE_NEM_FrontierValidatorInstance.after_step,`NGE_NEQ_LateBorrow.after_preserves_child,`NGE_NEQ_ResultValidator.ordered_effects] : Array Name) do
  let entry := match env.find? n with
   | none => Json.mkObj [("name",toJson n.toString),("found",toJson false)]
   | some ci => Json.mkObj [("name",toJson n.toString),("found",toJson true),
       ("is_theorem",toJson ci.isTheorem),("module_idx",toJson (reprStr ((env.getModuleIdxFor? n).map ModuleIdx.toNat))),
       ("type",toJson (reprStr ci.type))]
  logInfo m!"NGE_CERT_ENTRY {entry.compress}"
