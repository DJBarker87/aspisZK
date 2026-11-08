import NNH_Run5bHost
import NNH_S1CodecOk
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_CommonAssociation
open Aeneas Aeneas.Std Result
/-- Source common theorem, then inverse of the SAME decoded statement carrier.
No nominal-variant rewrite of the enclosing stage1 body is used. -/
theorem common (st : AspisS6CurrentCodecInstallation.Statement) :
 NMT_345Dec.toT7 (NMT_345.commonValue (NNH_S1DecodeOk.carrier st)) =
 NFY_NBN_StatementResult.common
  (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 st) := by
 rw [NMT_345.common_transport]
 exact congrArg NFY_NBN_StatementResult.common (NMT_345Dec.fromT8_inverse _)

theorem afterstate (st : AspisS6CurrentCodecInstallation.Statement) :
 NMT_345Dec.toT5 (NMT_345.commonValue (NNH_S1DecodeOk.carrier st)).lane_transition.candidate_afterstate =
 (NFY_NBN_StatementResult.common
  (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 st)).lane_transition.candidate_afterstate :=
 congrArg (fun c => c.lane_transition.candidate_afterstate) (common st)
#print axioms common
#print axioms afterstate
end AspisR1.NNV_CommonAssociation
end
