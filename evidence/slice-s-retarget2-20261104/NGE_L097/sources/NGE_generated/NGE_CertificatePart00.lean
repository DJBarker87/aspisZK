import Lean
import NGE_COMBINED_IMPORT
open Lean
run_cmd do
 let env ← getEnv
 logInfo m!"NGE_CERT_MODULES {(toJson (env.header.moduleNames.map (fun n => n.toString))).compress}"
 for n in (#[`NEQ_UnwrapDomains.fixed_read_packet,`NEX_FirstError.at_error,`NEY_Field00.alignment,`NEY_Field14.alignment,`NEY_ResultConstants.layout,`NFY_NED_PaymentValidation.withdrawal_result,`NFY_NEM_LaneReached.lane_reached,`NFY_NEQ_DecodeScalar.digest_word_domain,`NFY_NEU_BoxModel.withdrawal_result_state_effects,`NFY_NEU_ReconstructCore.result_state_effects,`NFY_NFD_CommonField05.alignment,`NFY_NFD_EmitProjection.alignment4,`NFY_NFD_RequestField03.alignment,`NFY_NFD_RequestProjection.transfer_roundtrip,`NGE_NEJ_CommonSourceFrame.result_and_frame,`NGE_NEM_ArraySnapshotView.cover,`NGE_NEM_FrontierValidatorInstance.live_step,`NGE_NEQ_NullifierDomains.common_independent,`NGE_NEQ_RootFrame.assembled] : Array Name) do
  let entry := match env.find? n with
   | none => Json.mkObj [("name",toJson n.toString),("found",toJson false)]
   | some ci => Json.mkObj [("name",toJson n.toString),("found",toJson true),
       ("is_theorem",toJson ci.isTheorem),("module_idx",toJson (reprStr (env.getModuleIdxFor? n))),
       ("type",toJson (reprStr ci.type))]
  logInfo m!"NGE_CERT_ENTRY {entry.compress}"
