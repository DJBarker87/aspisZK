import Lean
import NGE_COMBINED_IMPORT
open Lean
run_cmd do
 let env ← getEnv
 for n in (#[`NEX_CommonOracle.result_state_effects,`NEX_ReadDomains.after_window,`NEY_Field05.alignment,`NEY_Field18.alignment,`NEY_ResultStores.stores_observe,`NFY_NED_ReconstructCarriers.parts_argument,`NFY_NEM_LateOracle.late_reached,`NFY_NEQ_DecodeScalar.digest_word_domain,`NFY_NEU_BoxModel.withdrawal,`NFY_NEU_ReconstructAdopted.result_state_effects,`NFY_NFD_CommonField02.alignment,`NFY_NFD_EmitProjection.alignment0,`NFY_NFD_RequestDomains.payment_window,`NFY_NFD_RequestField11.alignment,`NFY_NFJ_Comparison.same_buffer_lengths,`NGE_NEL_CommonOracle.substitution,`NGE_NEM_EncoderFrame.after_value_and_frame,`NGE_NEM_PaymentFrame.common_reserved,`NGE_NEQ_ParserCanonical.some_canonical,`NGE_NEQ_RootFrame.finish] : Array Name) do
  let entry := match env.find? n with
   | none => Json.mkObj [("name",toJson n.toString),("found",toJson false)]
   | some ci => Json.mkObj [("name",toJson n.toString),("found",toJson true),
       ("is_theorem",toJson ci.isTheorem),("module_idx",toJson (reprStr ((env.getModuleIdxFor? n).map ModuleIdx.toNat))),
       ("type",toJson (reprStr ci.type))]
  logInfo m!"NGE_CERT_ENTRY {entry.compress}"
