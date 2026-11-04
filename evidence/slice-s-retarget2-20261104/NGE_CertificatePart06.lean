import Lean
import NGE_COMBINED_IMPORT
open Lean
run_cmd do
 let env ← getEnv
 for n in (#[`NEX_BoxValueExt.snapshot,`NEX_ReadDomains.after_scalar,`NEY_Field04.alignment,`NEY_Field17.alignment,`NEY_ResultProjection.stores_spec,`NFY_NED_ReconstructCarriers.common_argument,`NFY_NEM_LaneReached.lane_reached,`NFY_NEQ_DecodeScalar.digest_result_state_effects,`NFY_NEU_BoxModel.validator,`NFY_NEU_DecoderProjections.withdrawal_ext,`NFY_NFD_CommonField01.alignment,`NFY_NFD_CommonField14.alignment,`NFY_NFD_RequestDomains.payment_length,`NFY_NFD_RequestField10.alignment,`NFY_NFJ_Comparison.nativeEqualityBridge,`NGE_NEL_CommonOracle.reached_argument,`NGE_NEM_EncoderFrame.after_step_and_bytes,`NGE_NEM_KindInstance.statement_window,`NGE_NEQ_NullifierDomains.statement_result_frame,`NGE_NEQ_RootFrame.cover] : Array Name) do
  let entry := match env.find? n with
   | none => Json.mkObj [("name",toJson n.toString),("found",toJson false)]
   | some ci => Json.mkObj [("name",toJson n.toString),("found",toJson true),
       ("is_theorem",toJson ci.isTheorem),("module_idx",toJson (reprStr ((env.getModuleIdxFor? n).map ModuleIdx.toNat))),
       ("type",toJson (reprStr ci.type))]
  logInfo m!"NGE_CERT_ENTRY {entry.compress}"
