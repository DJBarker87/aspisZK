import Lean
import NGI_COMBINED_IMPORT
open Lean
run_cmd do
 let env ← getEnv
 logInfo m!"NGI_CERT_MODULES {(toJson (env.header.moduleNames.map (fun n => n.toString))).compress}"
 for n in (#[`NGE_NEQ_EncoderDomains.header_length,`NGE_NEQ_EncoderDomains.reached_domains,`NGE_NEQ_LateBorrow.after_preserves_child,`NGE_NEQ_LateBorrow.poststate,`NGE_NEQ_LateBorrow.rejoin,`NGE_NEQ_NullifierDomains.common_independent,`NGE_NEQ_NullifierDomains.payment_result_frame,`NGE_NEQ_NullifierDomains.statement_result_frame,`NGE_NEQ_ParserCanonical.some_canonical,`NGE_NEQ_PaymentDomains.fee_primitive_width,`NGE_NEQ_PaymentDomains.fee_zero,`NGE_NEQ_PaymentDomains.window_bounds,`NGE_NEQ_ResultValidator.after_domain,`NGE_NEQ_ResultValidator.call_shape,`NGE_NEQ_ResultValidator.lane_domain,`NGE_NEQ_ResultValidator.ordered_effects,`NGE_NEQ_ResultValidator.result,`NGE_NEQ_ResultValidator.result_state_effects,`NGE_NEQ_RootFrame.array_ext,`NGE_NEQ_RootFrame.assembled,`NGE_NEQ_RootFrame.cover,`NGE_NEQ_RootFrame.finish,`NGE_NEQ_RootFrame.header_frame,`NGE_NEQ_RootFrame.scalar_frame,`NGF_NEX_AfterDecodeOracle.result_state_effects,`NGF_NEX_AfterstateBox.child_packet,`NGF_NEX_AfterstateBox.result_state_effects,`NGF_NEX_AfterstateBox.value_ext,`NGF_NEX_BoxValueExt.late,`NGF_NEX_BoxValueExt.snapshot,`NGF_NEX_CommonOracle.result_state_effects,`NGF_NEX_DecoderDomains.common_reads,`NGF_NEX_DecoderDomains.common_windows,`NGF_NEX_DecoderDomains.late_windows,`NGF_NEX_DigestCallDomains.after_digest,`NGF_NEX_DigestCallDomains.exact_after,`NGF_NEX_DigestCallDomains.snapshot_digest,`NGF_NEX_FirstError.at_error,`NGF_NEX_FirstError.before,`NGF_NEX_FirstError.bounded,`NGF_NEX_LaneOracle.result_state_effects,`NGF_NEX_LateOracle.result_state_effects,`NGF_NEX_ReadDomains.after_scalar] : Array Name) do
  let entry := match env.find? n with
   | none => Json.mkObj [("name",toJson n.toString),("found",toJson false)]
   | some ci => Json.mkObj [("name",toJson n.toString),("found",toJson true),
       ("is_theorem",toJson ci.isTheorem),("module_idx",toJson ((env.getModuleIdxFor? n).map ModuleIdx.toNat)),
       ("type",toJson (reprStr ci.type))]
  logInfo m!"NGI_CERT_ENTRY {entry.compress}"
