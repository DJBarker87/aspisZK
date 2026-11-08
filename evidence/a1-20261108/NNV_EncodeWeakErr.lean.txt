import NNV_EncodeReflects
import NNV_AdapterEncodeHost
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_EncodeWeakErr
open Aeneas Aeneas.Std Result NNH_Run5bCtx NNH_Libraries

theorem source {W Tx : Type} (c : Ctx W Tx) (st : AspisS6CurrentCodecInstallation.Statement)
 (out : Array U8 688#usize)
 (called : (sdk c).op24 (AspisS6CurrentAdapterCarrier.fromPoolV1PairVerifiedAfterstateV1
  (NFY_NBN_StatementResult.common
   (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 st)).lane_transition.candidate_afterstate) = .ok (.Ok out)) :
 C.encodeCandidate (NNH_S1DecodeOk.carrier st) = some (out.val.map NMT_345.byte) := by
 rw [NNV_AdapterEncodeHost.slot] at called
 have run := NNV_EncodeReflects.source _ out called
 rw [NNV_AfterstatePort.source] at run
 change LIBC_S1.encode (NNH_S1DecodeOk.carrier st) = _
 unfold LIBC_S1.encode
 rw [run]

theorem rejected {W Tx : Type} (c : Ctx W Tx) (st : AspisS6CurrentCodecInstallation.Statement)
 (bad : C.encodeCandidate (NNH_S1DecodeOk.carrier st) = none) :
 ¬ ∃ out, (sdk c).op24 (AspisS6CurrentAdapterCarrier.fromPoolV1PairVerifiedAfterstateV1
  (NFY_NBN_StatementResult.common
   (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 st)).lane_transition.candidate_afterstate) = .ok (.Ok out) := by
 rintro ⟨out,called⟩
 have good := source c st out called
 rw [bad] at good
 cases good
#print axioms source
#print axioms rejected
end AspisR1.NNV_EncodeWeakErr
end
