import NNV_AdapterCommon
import NNV_AdapterEncodeHost
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNX_CommonEncode
open Aeneas Aeneas.Std Result NNH_Run5bCtx
/-- Source getter/encoder diagram on the SAME statement. Every ambient and
returned arm is retained, including the literal host's rejected-encode div. -/
theorem source {W Tx : Type} (c : Ctx W Tx)
 (st : AspisS6CurrentCodecInstallation.Statement) :
 (do let common ← AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common st
     (sdk c).op24 common.lane_transition.candidate_afterstate) =
 (match NMT_345.encodeCall
   (NMT_345.commonValue (NNH_S1DecodeOk.carrier st)).lane_transition.candidate_afterstate with
  | .ok (.Ok out) => .ok (.Ok out)
  | .ok (.Err _) => .div
  | .fail e => .fail e
  | .div => .div) := by
 rw [NNV_AdapterCommon.source]
 simp only [bind_tc_ok]
 rw [NNV_AdapterEncodeHost.slot]
 unfold NNH_S1HostCodec.encode
 have getter :
  (AspisS6CurrentAdapterCarrier.fromPoolV1PairForestTerminalCommonV1
   (NFY_NBN_StatementResult.common
    (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 st))).lane_transition.candidate_afterstate =
  AspisS6CurrentAdapterCarrier.fromPoolV1PairVerifiedAfterstateV1
   (NFY_NBN_StatementResult.common
    (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 st)).lane_transition.candidate_afterstate := by rfl
 rw [getter,NNV_AfterstatePort.source]
 rfl
#print axioms source
end AspisR1.NNX_CommonEncode
end
