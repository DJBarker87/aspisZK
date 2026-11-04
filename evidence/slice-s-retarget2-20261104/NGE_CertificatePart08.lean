import Lean
import NGE_COMBINED_IMPORT
open Lean
run_cmd do
 let env ← getEnv
 for n in (#[`NEX_DecoderDomains.common_reads,`NEX_ReadDomains.disjoint,`NEY_Field06.alignment,`NEY_Field19.alignment,`NEY_TerminalGeometry.header_constants,`NFY_NED_ScannerCohorts.account_body,`NFY_NEM_LateOracle.run_substitution,`NFY_NEQ_DecodeScalar.header_result_state_effects,`NFY_NEU_BoxModel.withdrawal_result_state_effects,`NFY_NEU_ReconstructCore.common_result,`NFY_NFD_CommonField03.alignment,`NFY_NFD_EmitProjection.alignment1,`NFY_NFD_RequestDomains.wrong_length,`NFY_NFD_RequestField12.alignment,`NFY_NFJ_Comparison.slot_zero_iff,`NGE_NEL_DigestLoopFrame.step_and_bytes,`NGE_NEM_EncoderFrame.fill_value,`NGE_NEM_PaymentFrame.transfer_reply,`NGE_NEQ_PaymentDomains.fee_primitive_width,`NGE_NEQ_RootFrame.header_frame] : Array Name) do
  let entry := match env.find? n with
   | none => Json.mkObj [("name",toJson n.toString),("found",toJson false)]
   | some ci => Json.mkObj [("name",toJson n.toString),("found",toJson true),
       ("is_theorem",toJson ci.isTheorem),("module_idx",toJson (reprStr ((env.getModuleIdxFor? n).map ModuleIdx.toNat))),
       ("type",toJson (reprStr ci.type))]
  logInfo m!"NGE_CERT_ENTRY {entry.compress}"
