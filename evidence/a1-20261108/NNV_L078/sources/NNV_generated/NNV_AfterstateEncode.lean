import NNV_AfterstatePort
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_AfterstateEncode
open Aeneas Aeneas.Std Result NNH_Libraries

theorem returned (st : AspisS6CurrentCodecInstallation.Statement) (bytes : RSL.Bytes)
 (encoded : C.encodeCandidate (NNH_S1DecodeOk.carrier st) = some bytes) :
 ∃ out : Array U8 688#usize,
 NNH_S1HostCodec.encode (AspisS6CurrentAdapterCarrier.fromPoolV1PairVerifiedAfterstateV1
  (NFY_NBN_StatementResult.common
   (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 st)).lane_transition.candidate_afterstate) =
 .ok (.Ok out) ∧ out.val.map NMT_345.byte = bytes := by
 obtain ⟨out,call,image⟩ := NNH_S1CodecOk.encode (NNH_S1DecodeOk.carrier st) bytes encoded
 refine ⟨out,?_,image⟩
 apply NNH_S1HostCodec.encode_ok
 rw [NNV_AfterstatePort.source]
 exact call
#print axioms returned
end AspisR1.NNV_AfterstateEncode
end
