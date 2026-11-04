import Lean
import NGE_COMBINED_IMPORT
open Lean
run_cmd do
 let env ← getEnv
 for n in (#[`NEX_AfterstateBox.result_state_effects,`NEX_FirstError.bounded,`NEY_Field01.alignment,`NEY_Field14.alignment,`NEY_ReachedResultDomains.ready_payload,`NFY_NED_PaymentCohorts.withdrawal_common,`NFY_NEJ_CommonFrame.common_bytes,`NFY_NEM_ValidatorComposed.result_state_effects,`NFY_NEU_BoxDecodeModel.withdrawal_result_state_effects,`NFY_NEU_DecoderProjections.common_ext,`NFY_NEY_EmitComposed.result_state_effects,`NFY_NFD_CommonField11.alignment,`NFY_NFD_RawCarriers.tag_result_state_effects,`NFY_NFD_RequestField07.alignment,`NFY_NFD_WideSerialization.result_state_effects,`NGE_NEJ_ScannerWidth.width,`NGE_NEM_ArraySnapshotView.poststate,`NGE_NEM_FrontierValidatorInstance.live_step,`NGE_NEQ_LateBorrow.rejoin,`NGE_NEQ_ResultValidator.result_state_effects] : Array Name) do
  let entry := match env.find? n with
   | none => Json.mkObj [("name",toJson n.toString),("found",toJson false)]
   | some ci => Json.mkObj [("name",toJson n.toString),("found",toJson true),
       ("is_theorem",toJson ci.isTheorem),("module_idx",toJson (reprStr ((env.getModuleIdxFor? n).map ModuleIdx.toNat))),
       ("type",toJson (reprStr ci.type))]
  logInfo m!"NGE_CERT_ENTRY {entry.compress}"
