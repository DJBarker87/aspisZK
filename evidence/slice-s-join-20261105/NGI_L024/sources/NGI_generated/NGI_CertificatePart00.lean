import Lean
import NGI_COMBINED_IMPORT
open Lean
run_cmd do
 let env ← getEnv
 logInfo m!"NGI_CERT_MODULES {(toJson (env.header.moduleNames.map (fun n => n.toString))).compress}"
 for n in (#[`NEQ_UnwrapDomains.err_result_state_effects,`NEQ_UnwrapDomains.fixed_read_packet,`NEQ_UnwrapDomains.ok_result_state_effects,`NEX_Exact.result_state_effects,`NFY_NED_CommonValidation.common_result,`NFY_NED_DigestCohorts.first_byte,`NFY_NED_PaymentCohorts.canonical_result,`NFY_NED_PaymentCohorts.transfer_common,`NFY_NED_PaymentCohorts.withdrawal_common,`NFY_NED_PaymentValidation.transfer_result,`NFY_NED_PaymentValidation.withdrawal_result,`NFY_NED_ReconstructCarriers.common_argument,`NFY_NED_ReconstructCarriers.parts_argument,`NFY_NED_ScannerCohorts.account_body,`NFY_NED_ScannerCohorts.account_result,`NFY_NED_ScannerCohorts.profile_body,`NFY_NED_ScannerCohorts.profile_result,`NFY_NED_SubtreeComposition.first_byte,`NFY_NEE_M31SerializerDomain.primitive,`NFY_NEE_M31SerializerDomain.width,`NFY_NEE_M31SerializerDomain.widths_distinct,`NFY_NEJ_CommonFrame.common_bytes,`NFY_NEL_CopyArrayLaw.loop_binding,`NFY_NEM_LaneReached.lane_instance,`NFY_NEM_LaneReached.lane_reached,`NFY_NEM_LateOracle.late_reached,`NFY_NEM_LateOracle.run_substitution,`NFY_NEM_LateOracle.tail_substitution,`NFY_NEM_LateOracle.value_and_frame,`NFY_NEM_PaymentReached.payment_instance,`NFY_NEM_PaymentReached.payment_reached,`NFY_NEM_SnapshotBorrow.after_preserves_child,`NFY_NEM_SnapshotBorrow.poststate,`NFY_NEM_SnapshotBorrow.rejoin,`NFY_NEM_ValidatorComposed.result_state_effects,`NFY_NEQ_CommonDecode.result_state_effects,`NFY_NEQ_CommonDecode.substitution,`NFY_NEQ_DecodeScalar.digest_result_state_effects,`NFY_NEQ_DecodeScalar.digest_word_domain,`NFY_NEQ_DecodeScalar.header_result_state_effects,`NFY_NEQ_DecodeScalar.m31_result_state_effects,`NFY_NEQ_EncoderOracle.result_state_effects,`NFY_NEQ_EncoderOracle.substitution] : Array Name) do
  let entry := match env.find? n with
   | none => Json.mkObj [("name",toJson n.toString),("found",toJson false)]
   | some ci => Json.mkObj [("name",toJson n.toString),("found",toJson true),
       ("is_theorem",toJson ci.isTheorem),("module_idx",toJson ((env.getModuleIdxFor? n).map ModuleIdx.toNat)),
       ("type",toJson (reprStr ci.type))]
  logInfo m!"NGI_CERT_ENTRY {entry.compress}"
