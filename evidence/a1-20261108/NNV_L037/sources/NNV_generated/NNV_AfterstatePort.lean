import NNV_CommonAssociation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_AfterstatePort
open Aeneas Aeneas.Std Result
/-- The SAME source afterstate, returned to the adapter carrier, is the encoder
argument corresponding to the decoded statement's common value. -/
theorem source (st : AspisS6CurrentCodecInstallation.Statement) :
 NNH_S1HostCodec.afterCarrier
  (AspisS6CurrentAdapterCarrier.fromPoolV1PairVerifiedAfterstateV1
   (NFY_NBN_StatementResult.common
    (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 st)).lane_transition.candidate_afterstate) =
 (NMT_345.commonValue (NNH_S1DecodeOk.carrier st)).lane_transition.candidate_afterstate := by
 unfold NNH_S1HostCodec.afterCarrier
 rw [AspisS6CurrentAdapterCarrier.to_fromPoolV1PairVerifiedAfterstateV1]
 calc
  _ = NMT_345Dec.fromT5 (NMT_345Dec.toT5
    (NMT_345.commonValue (NNH_S1DecodeOk.carrier st)).lane_transition.candidate_afterstate) :=
   congrArg NMT_345Dec.fromT5 (NNV_CommonAssociation.afterstate st).symm
  _ = _ := NMT_345Dec.toT5_inverse _
#print axioms source
end AspisR1.NNV_AfterstatePort
end
