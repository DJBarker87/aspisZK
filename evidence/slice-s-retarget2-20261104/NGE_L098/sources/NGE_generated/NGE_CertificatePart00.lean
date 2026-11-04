import Lean
import NGE_COMBINED_IMPORT
open Lean
run_cmd do
 let env ← getEnv
 logInfo m!"NGE_CERT_MODULES {(toJson (env.header.moduleNames.map (fun n => n.toString))).compress}"
 for n in (#[`NEQ_UnwrapDomains.fixed_read_packet,`NEX_DigestCallDomains.snapshot_digest,`NEX_TerminalDomain.fixed_carrier,`NEY_Field11.alignment,`NEY_Field24.alignment,`NFY_NED_DigestCohorts.first_byte,`NFY_NEE_M31SerializerDomain.primitive,`NFY_NEM_SnapshotBorrow.after_preserves_child,`NFY_NEQ_PaymentDecode.withdrawal_result_state_effects,`NFY_NEU_CallDomains.withdrawal_packet,`NFY_NEY_BindingSuccess.binding_success,`NFY_NFD_CommonField08.alignment,`NFY_NFD_EmitProjection.alignment6,`NFY_NFD_RequestField04.alignment,`NFY_NFD_RequestProjection.transfer_roundtrip,`NGE_NEE_CanonicalFrame.tree_body,`NGE_NEL_PaymentOracle.withdrawal_call_count,`NGE_NEM_FrontierValidatorInstance.after_result_and_frame,`NGE_NEQ_EncoderDomains.reached_domains,`NGE_NEQ_ResultValidator.lane_domain] : Array Name) do
  let entry := match env.find? n with
   | none => Json.mkObj [("name",toJson n.toString),("found",toJson false)]
   | some ci => Json.mkObj [("name",toJson n.toString),("found",toJson true),
       ("is_theorem",toJson ci.isTheorem),("module_idx",toJson (reprStr ((env.getModuleIdxFor? n).map ModuleIdx.toNat))),
       ("type",toJson (reprStr ci.type))]
  logInfo m!"NGE_CERT_ENTRY {entry.compress}"
