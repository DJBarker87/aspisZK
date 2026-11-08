import NNV_AfterstateEncode
import NNH_Run5bHost
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_AdapterEncodeHost
open Aeneas Aeneas.Std Result NNH_Run5bCtx

theorem slot {W Tx : Type} (c : Ctx W Tx) (a : NNH_S1HostCodec.Afterstate) :
 (sdk c).op24 a = NNH_S1HostCodec.encode a := rfl

theorem returned {W Tx : Type} (c : Ctx W Tx)
 (st : AspisS6CurrentCodecInstallation.Statement) (bytes : RSL.Bytes)
 (encoded : NNH_Libraries.C.encodeCandidate (NNH_S1DecodeOk.carrier st) = some bytes) :
 ∃ out : Array U8 688#usize,
 (sdk c).op24 (AspisS6CurrentAdapterCarrier.fromPoolV1PairVerifiedAfterstateV1
  (NFY_NBN_StatementResult.common
   (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 st)).lane_transition.candidate_afterstate) =
 .ok (.Ok out) ∧ out.val.map NMT_345.byte = bytes := by
 obtain ⟨out,run,image⟩ := NNV_AfterstateEncode.returned st bytes encoded
 exact ⟨out,(slot c _).trans run,image⟩
#print axioms slot
#print axioms returned
end AspisR1.NNV_AdapterEncodeHost
end
