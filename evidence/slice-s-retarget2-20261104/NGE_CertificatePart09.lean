import Lean
import NGE_COMBINED_IMPORT
open Lean
run_cmd do
 let env ← getEnv
 for n in (#[`NEX_DecoderDomains.common_windows,`NEX_ReadDomains.snapshot_window,`NEY_Field07.alignment,`NEY_Field20.alignment,`NEY_TerminalGeometry.kind_same,`NFY_NED_ScannerCohorts.account_result,`NFY_NEM_LateOracle.tail_substitution,`NFY_NEQ_EncoderOracle.result_state_effects,`NFY_NEU_CallDomains.common_packet,`NFY_NEU_ReconstructCore.result_state_effects,`NFY_NFD_CommonField04.alignment,`NFY_NFD_EmitProjection.alignment2,`NFY_NFD_RequestField00.alignment,`NFY_NFD_RequestField13.alignment,`NFY_NFJ_Scanner.decode_domain,`NGE_NEL_PaymentFieldCarriers.transfer_fields,`NGE_NEM_EncoderFrame.frontier_next,`NGE_NEM_PaymentFrame.withdrawal_reply,`NGE_NEQ_PaymentDomains.fee_zero,`NGE_NEQ_RootFrame.scalar_frame] : Array Name) do
  let entry := match env.find? n with
   | none => Json.mkObj [("name",toJson n.toString),("found",toJson false)]
   | some ci => Json.mkObj [("name",toJson n.toString),("found",toJson true),
       ("is_theorem",toJson ci.isTheorem),("module_idx",toJson (reprStr ((env.getModuleIdxFor? n).map ModuleIdx.toNat))),
       ("type",toJson (reprStr ci.type))]
  logInfo m!"NGE_CERT_ENTRY {entry.compress}"
