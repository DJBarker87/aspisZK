import Lean
import NGE_COMBINED_IMPORT
open Lean
run_cmd do
 let env ← getEnv
 for n in (#[`NEX_DigestCallDomains.after_digest,`NEX_SnapshotParent.result_state_effects,`NEY_Field09.alignment,`NEY_Field22.alignment,`NEY_TerminalGeometry.payment_window,`NFY_NED_ScannerCohorts.profile_result,`NFY_NEM_PaymentReached.payment_instance,`NFY_NEQ_PaymentDecode.transfer_result_state_effects,`NFY_NEU_CallDomains.transfer_packet,`NFY_NEX_TerminalOracle.result_state_effects,`NFY_NFD_CommonField06.alignment,`NFY_NFD_EmitProjection.alignment4,`NFY_NFD_RequestField02.alignment,`NFY_NFD_RequestOracle.result_state_effects,`NFY_NFJ_Scanner.result_state_effects,`NGE_NEL_PaymentOracle.transfer_call_count,`NGE_NEM_EncoderFrame.live_value_and_frame,`NGE_NEQ_BorrowWidth.status,`NGE_NEQ_ResultValidator.after_domain] : Array Name) do
  let entry := match env.find? n with
   | none => Json.mkObj [("name",toJson n.toString),("found",toJson false)]
   | some ci => Json.mkObj [("name",toJson n.toString),("found",toJson true),
       ("is_theorem",toJson ci.isTheorem),("module_idx",toJson (reprStr ((env.getModuleIdxFor? n).map ModuleIdx.toNat))),
       ("type",toJson (reprStr ci.type))]
  logInfo m!"NGE_CERT_ENTRY {entry.compress}"
