import Lean
import NGE_COMBINED_IMPORT
open Lean
run_cmd do
 let env ← getEnv
 for n in (#[`NEX_BoxValueExt.late,`NEX_LateOracle.result_state_effects,`NEY_Field03.alignment,`NEY_Field16.alignment,`NEY_ResultConstants.partition,`NFY_NED_PaymentValidation.withdrawal_result,`NFY_NEM_LaneReached.lane_instance,`NFY_NEQ_CommonDecode.substitution,`NFY_NEU_BoxModel.transfer_result_state_effects,`NFY_NEU_DecoderProjections.transfer_ext,`NFY_NFD_CommonField00.alignment,`NFY_NFD_CommonField13.alignment,`NFY_NFD_RequestDomains.binding_fields,`NFY_NFD_RequestField09.alignment,`NFY_NFJ_Comparison.header_length,`NGE_NEL_CommonOracle.call_count,`NGE_NEM_DigestInstance.result_and_frame,`NGE_NEM_KindInstance.payment_window,`NGE_NEQ_NullifierDomains.payment_result_frame,`NGE_NEQ_RootFrame.assembled] : Array Name) do
  let entry := match env.find? n with
   | none => Json.mkObj [("name",toJson n.toString),("found",toJson false)]
   | some ci => Json.mkObj [("name",toJson n.toString),("found",toJson true),
       ("is_theorem",toJson ci.isTheorem),("module_idx",toJson (reprStr ((env.getModuleIdxFor? n).map ModuleIdx.toNat))),
       ("type",toJson (reprStr ci.type))]
  logInfo m!"NGE_CERT_ENTRY {entry.compress}"
