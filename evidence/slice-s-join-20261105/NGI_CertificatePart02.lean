import Lean
import NGI_COMBINED_IMPORT
open Lean
run_cmd do
 let env ← getEnv
 logInfo m!"NGI_CERT_MODULES {(toJson (env.header.moduleNames.map (fun n => n.toString))).compress}"
 for n in (#[`NFY_NFD_CommonField11.alignment,`NFY_NFD_CommonField12.alignment,`NFY_NFD_CommonField13.alignment,`NFY_NFD_CommonField14.alignment,`NFY_NFD_EmitProjection.alignment0,`NFY_NFD_EmitProjection.alignment1,`NFY_NFD_EmitProjection.alignment2,`NFY_NFD_EmitProjection.alignment3,`NFY_NFD_EmitProjection.alignment4,`NFY_NFD_EmitProjection.alignment5,`NFY_NFD_EmitProjection.alignment6,`NFY_NFD_EmitProjection.alignment7,`NFY_NFD_EmitProjection.complete,`NFY_NFD_RawCarriers.tag_result_state_effects,`NFY_NFD_RawCarriers.tag_roundtrip,`NFY_NFD_RequestDomains.binding_fields,`NFY_NFD_RequestDomains.payment_length,`NFY_NFD_RequestDomains.payment_window,`NFY_NFD_RequestDomains.wrong_length,`NFY_NFD_RequestField00.alignment,`NFY_NFD_RequestField01.alignment,`NFY_NFD_RequestField02.alignment,`NFY_NFD_RequestField03.alignment,`NFY_NFD_RequestField04.alignment,`NFY_NFD_RequestField05.alignment,`NFY_NFD_RequestField06.alignment,`NFY_NFD_RequestField07.alignment,`NFY_NFD_RequestField08.alignment,`NFY_NFD_RequestField09.alignment,`NFY_NFD_RequestField10.alignment,`NFY_NFD_RequestField11.alignment,`NFY_NFD_RequestField12.alignment,`NFY_NFD_RequestField13.alignment,`NFY_NFD_RequestOracle.array_result_state_effects,`NFY_NFD_RequestOracle.result_state_effects,`NFY_NFD_RequestProjection.complete,`NFY_NFD_RequestProjection.transfer_roundtrip,`NFY_NFD_RequestProjection.withdrawal_roundtrip,`NFY_NFD_WideSerialization.carrier_roundtrip,`NFY_NFD_WideSerialization.result_state_effects,`NFY_NFJ_Comparison.completion,`NFY_NFJ_Comparison.header_length,`NFY_NFJ_Comparison.nativeEqualityBridge] : Array Name) do
  let entry := match env.find? n with
   | none => Json.mkObj [("name",toJson n.toString),("found",toJson false)]
   | some ci => Json.mkObj [("name",toJson n.toString),("found",toJson true),
       ("is_theorem",toJson ci.isTheorem),("module_idx",toJson ((env.getModuleIdxFor? n).map ModuleIdx.toNat)),
       ("type",toJson (reprStr ci.type))]
  logInfo m!"NGI_CERT_ENTRY {entry.compress}"
