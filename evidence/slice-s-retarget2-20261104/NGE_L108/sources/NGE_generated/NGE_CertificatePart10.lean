import Lean
import NGE_COMBINED_IMPORT
open Lean
run_cmd do
 let env ← getEnv
 for n in (#[`NEX_DecoderDomains.late_windows,`NEX_SnapshotBoxOracle.result_state_effects,`NEY_Field08.alignment,`NEY_Field21.alignment,`NEY_TerminalGeometry.payment_offset,`NFY_NED_ScannerCohorts.profile_body,`NFY_NEM_LateOracle.value_and_frame,`NFY_NEQ_EncoderOracle.substitution,`NFY_NEU_CallDomains.reached_domains,`NFY_NEX_PublicModel.result_state_effects,`NFY_NFD_CommonField05.alignment,`NFY_NFD_EmitProjection.alignment3,`NFY_NFD_RequestField01.alignment,`NFY_NFD_RequestOracle.array_result_state_effects,`NFY_NFJ_Scanner.encode_domain,`NGE_NEL_PaymentFieldCarriers.withdrawal_fields,`NGE_NEM_EncoderFrame.live_step_and_bytes,`NGE_NEQ_BorrowWidth.fixed216,`NGE_NEQ_PaymentDomains.window_bounds] : Array Name) do
  let entry := match env.find? n with
   | none => Json.mkObj [("name",toJson n.toString),("found",toJson false)]
   | some ci => Json.mkObj [("name",toJson n.toString),("found",toJson true),
       ("is_theorem",toJson ci.isTheorem),("module_idx",toJson (reprStr ((env.getModuleIdxFor? n).map ModuleIdx.toNat))),
       ("type",toJson (reprStr ci.type))]
  logInfo m!"NGE_CERT_ENTRY {entry.compress}"
