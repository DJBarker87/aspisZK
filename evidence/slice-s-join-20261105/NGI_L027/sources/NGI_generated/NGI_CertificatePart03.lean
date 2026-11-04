import Lean
import NGI_COMBINED_IMPORT
open Lean
run_cmd do
 let env ← getEnv
 logInfo m!"NGI_CERT_MODULES {(toJson (env.header.moduleNames.map (fun n => n.toString))).compress}"
 for n in (#[`NFY_NFJ_Comparison.same_buffer_lengths,`NFY_NFJ_Comparison.slot_zero_iff,`NFY_NFJ_Scanner.decode_domain,`NFY_NFJ_Scanner.encode_domain,`NFY_NFJ_Scanner.result_state_effects,`NFY_NFJ_Scanner.tag_domain,`NGE_NEE_CanonicalFrame.tree_body,`NGE_NEJ_CommonSourceFrame.result_and_frame,`NGE_NEJ_ScannerFramed.value_and_frame,`NGE_NEJ_ScannerWidth.width,`NGE_NEJ_WindowStep.iteration,`NGE_NEL_CommonOracle.call_count,`NGE_NEL_CommonOracle.reached_argument,`NGE_NEL_CommonOracle.substitution,`NGE_NEL_DigestLoopFrame.step_and_bytes,`NGE_NEL_PaymentFieldCarriers.transfer_fields,`NGE_NEL_PaymentFieldCarriers.withdrawal_fields,`NGE_NEL_PaymentOracle.transfer_call_count,`NGE_NEL_PaymentOracle.transfer_substitution,`NGE_NEL_PaymentOracle.withdrawal_call_count,`NGE_NEL_PaymentOracle.withdrawal_substitution,`NGE_NEM_ArraySnapshotView.cover,`NGE_NEM_ArraySnapshotView.poststate,`NGE_NEM_DigestInstance.next_call,`NGE_NEM_DigestInstance.result_and_frame,`NGE_NEM_EncoderFrame.after_step_and_bytes,`NGE_NEM_EncoderFrame.after_value_and_frame,`NGE_NEM_EncoderFrame.fill_value,`NGE_NEM_EncoderFrame.frontier_next,`NGE_NEM_EncoderFrame.live_step_and_bytes,`NGE_NEM_EncoderFrame.live_value_and_frame,`NGE_NEM_EncoderReceiver.sequence_width,`NGE_NEM_FrontierValidatorInstance.after_result_and_frame,`NGE_NEM_FrontierValidatorInstance.after_step,`NGE_NEM_FrontierValidatorInstance.live_result_and_frame,`NGE_NEM_FrontierValidatorInstance.live_step,`NGE_NEM_KindInstance.parser_result_frame,`NGE_NEM_KindInstance.payment_window,`NGE_NEM_KindInstance.statement_window,`NGE_NEM_PaymentFrame.common_reserved,`NGE_NEM_PaymentFrame.transfer_reply,`NGE_NEM_PaymentFrame.withdrawal_reply,`NGE_NEQ_BorrowWidth.fixed216,`NGE_NEQ_BorrowWidth.status] : Array Name) do
  let entry := match env.find? n with
   | none => Json.mkObj [("name",toJson n.toString),("found",toJson false)]
   | some ci => Json.mkObj [("name",toJson n.toString),("found",toJson true),
       ("is_theorem",toJson ci.isTheorem),("module_idx",toJson ((env.getModuleIdxFor? n).map ModuleIdx.toNat)),
       ("type",toJson (reprStr ci.type))]
  logInfo m!"NGI_CERT_ENTRY {entry.compress}"
