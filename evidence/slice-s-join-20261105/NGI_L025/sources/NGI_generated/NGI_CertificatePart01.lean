import Lean
import NGI_COMBINED_IMPORT
open Lean
run_cmd do
 let env ← getEnv
 logInfo m!"NGI_CERT_MODULES {(toJson (env.header.moduleNames.map (fun n => n.toString))).compress}"
 for n in (#[`NFY_NEQ_PaymentDecode.transfer_result_state_effects,`NFY_NEQ_PaymentDecode.transfer_substitution,`NFY_NEQ_PaymentDecode.withdrawal_result_state_effects,`NFY_NEQ_PaymentDecode.withdrawal_substitution,`NFY_NEU_BoxDecodeModel.transfer_result_state_effects,`NFY_NEU_BoxDecodeModel.withdrawal_result_state_effects,`NFY_NEU_BoxModel.transfer,`NFY_NEU_BoxModel.transfer_result_state_effects,`NFY_NEU_BoxModel.validator,`NFY_NEU_BoxModel.withdrawal,`NFY_NEU_BoxModel.withdrawal_result_state_effects,`NFY_NEU_CallDomains.common_packet,`NFY_NEU_CallDomains.reached_domains,`NFY_NEU_CallDomains.transfer_packet,`NFY_NEU_CallDomains.transfer_reply_range,`NFY_NEU_CallDomains.withdrawal_packet,`NFY_NEU_CallDomains.withdrawal_reply_range,`NFY_NEU_CommonProjections.common_ext,`NFY_NEU_DecoderProjections.common_ext,`NFY_NEU_DecoderProjections.payment_packet,`NFY_NEU_DecoderProjections.transfer_ext,`NFY_NEU_DecoderProjections.withdrawal_ext,`NFY_NEU_ReconstructAdopted.result_state_effects,`NFY_NEU_ReconstructCore.common_result,`NFY_NEU_ReconstructCore.result_state_effects,`NFY_NEX_PublicModel.result_state_effects,`NFY_NEX_TerminalOracle.result_state_effects,`NFY_NEY_BindingContinuation.result,`NFY_NEY_BindingSuccess.binding_success,`NFY_NEY_EmitComposed.encoder_bridge,`NFY_NEY_EmitComposed.reached_encoder,`NFY_NEY_EmitComposed.result_state_effects,`NFY_NEY_ResultEncoderOracle.result_state_effects,`NFY_NFD_CommonField00.alignment,`NFY_NFD_CommonField01.alignment,`NFY_NFD_CommonField02.alignment,`NFY_NFD_CommonField03.alignment,`NFY_NFD_CommonField04.alignment,`NFY_NFD_CommonField05.alignment,`NFY_NFD_CommonField06.alignment,`NFY_NFD_CommonField07.alignment,`NFY_NFD_CommonField08.alignment,`NFY_NFD_CommonField09.alignment,`NFY_NFD_CommonField10.alignment] : Array Name) do
  let entry := match env.find? n with
   | none => Json.mkObj [("name",toJson n.toString),("found",toJson false)]
   | some ci => Json.mkObj [("name",toJson n.toString),("found",toJson true),
       ("is_theorem",toJson ci.isTheorem),("module_idx",toJson ((env.getModuleIdxFor? n).map ModuleIdx.toNat)),
       ("type",toJson (reprStr ci.type))]
  logInfo m!"NGI_CERT_ENTRY {entry.compress}"
