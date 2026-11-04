import Lean
import NGE_COMBINED_IMPORT
open Lean
run_cmd do
 let env ← getEnv
 for n in (#[`NEX_AfterstateBox.child_packet,`NEX_FirstError.before,`NEY_Field00.alignment,`NEY_Field13.alignment,`NEY_ReachedResultDomains.binding_argument,`NFY_NED_PaymentCohorts.transfer_common,`NFY_NEE_M31SerializerDomain.widths_distinct,`NFY_NEM_SnapshotBorrow.rejoin,`NFY_NEU_BoxDecodeModel.transfer_result_state_effects,`NFY_NEU_CommonProjections.common_ext,`NFY_NEY_EmitComposed.reached_encoder,`NFY_NFD_CommonField10.alignment,`NFY_NFD_EmitProjection.complete,`NFY_NFD_RequestField06.alignment,`NFY_NFD_WideSerialization.carrier_roundtrip,`NGE_NEJ_ScannerFramed.value_and_frame,`NGE_NEM_ArraySnapshotView.cover,`NGE_NEM_FrontierValidatorInstance.live_result_and_frame,`NGE_NEQ_LateBorrow.poststate,`NGE_NEQ_ResultValidator.result] : Array Name) do
  let entry := match env.find? n with
   | none => Json.mkObj [("name",toJson n.toString),("found",toJson false)]
   | some ci => Json.mkObj [("name",toJson n.toString),("found",toJson true),
       ("is_theorem",toJson ci.isTheorem),("module_idx",toJson (reprStr ((env.getModuleIdxFor? n).map ModuleIdx.toNat))),
       ("type",toJson (reprStr ci.type))]
  logInfo m!"NGE_CERT_ENTRY {entry.compress}"
