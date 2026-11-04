import Lean
import NGE_COMBINED_IMPORT
open Lean
run_cmd do
 let env ← getEnv
 for n in (#[`NEX_AfterstateBox.value_ext,`NEX_LaneOracle.result_state_effects,`NEY_Field02.alignment,`NEY_Field15.alignment,`NEY_ResultConstants.layout,`NFY_NED_PaymentValidation.transfer_result,`NFY_NEL_CopyArrayLaw.loop_binding,`NFY_NEQ_CommonDecode.result_state_effects,`NFY_NEU_BoxModel.transfer,`NFY_NEU_DecoderProjections.payment_packet,`NFY_NEY_ResultEncoderOracle.result_state_effects,`NFY_NFD_CommonField12.alignment,`NFY_NFD_RawCarriers.tag_roundtrip,`NFY_NFD_RequestField08.alignment,`NFY_NFJ_Comparison.completion,`NGE_NEJ_WindowStep.iteration,`NGE_NEM_DigestInstance.next_call,`NGE_NEM_KindInstance.parser_result_frame,`NGE_NEQ_NullifierDomains.common_independent,`NGE_NEQ_RootFrame.array_ext] : Array Name) do
  let entry := match env.find? n with
   | none => Json.mkObj [("name",toJson n.toString),("found",toJson false)]
   | some ci => Json.mkObj [("name",toJson n.toString),("found",toJson true),
       ("is_theorem",toJson ci.isTheorem),("module_idx",toJson (reprStr ((env.getModuleIdxFor? n).map ModuleIdx.toNat))),
       ("type",toJson (reprStr ci.type))]
  logInfo m!"NGE_CERT_ENTRY {entry.compress}"
