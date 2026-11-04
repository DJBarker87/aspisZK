import Lean
import NGE_COMBINED_IMPORT
open Lean
run_cmd do
 let env ← getEnv
 for n in (#[`NEX_DigestCallDomains.exact_after,`NEX_StatementExt.complete,`NEY_Field10.alignment,`NEY_Field23.alignment,`NFY_NED_CommonValidation.common_result,`NFY_NED_SubtreeComposition.first_byte,`NFY_NEM_PaymentReached.payment_reached,`NFY_NEQ_PaymentDecode.transfer_substitution,`NFY_NEU_CallDomains.transfer_reply_range,`NFY_NEY_BindingContinuation.result,`NFY_NFD_CommonField07.alignment,`NFY_NFD_EmitProjection.alignment5,`NFY_NFD_RequestField03.alignment,`NFY_NFD_RequestProjection.complete,`NFY_NFJ_Scanner.tag_domain,`NGE_NEL_PaymentOracle.transfer_substitution,`NGE_NEM_EncoderReceiver.sequence_width,`NGE_NEQ_EncoderDomains.header_length,`NGE_NEQ_ResultValidator.call_shape] : Array Name) do
  let entry := match env.find? n with
   | none => Json.mkObj [("name",toJson n.toString),("found",toJson false)]
   | some ci => Json.mkObj [("name",toJson n.toString),("found",toJson true),
       ("is_theorem",toJson ci.isTheorem),("module_idx",toJson (reprStr ((env.getModuleIdxFor? n).map ModuleIdx.toNat))),
       ("type",toJson (reprStr ci.type))]
  logInfo m!"NGE_CERT_ENTRY {entry.compress}"
