import NLB_Windows
set_option autoImplicit false
noncomputable section
namespace NLB_NativeFlush
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- Actual retained one-store fold; the original arbitrary full weight buffer
is the initial state. There is no source-output seed and no sparse buffer. -/
def G (pending : verifier.BatchedWeights) (weights : Slice aspis_core.field.QM31) :
 Slice aspis_core.field.QM31 :=
 ⟨NKE_FlushNative.states pending weights 64,
  by simpa only [NKE_FlushNative.states,NKE_Stores.length] using weights.property⟩

/-- NKO's source-domain and native all-store/frame induction identify the SAME
returned slice. Raw/terms/other-cell frames are the retained NKE/NJR steps. -/
theorem at_actual (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (pending : verifier.BatchedWeights) (weights : Slice aspis_core.field.QM31)
 (reply : Result (Slice aspis_core.field.QM31))
 (entered : Event.flush pending weights reply∈(run wr rr merkle finish d pub proof ck hash none).events) :
 ok (G pending weights)=reply := by
 obtain ⟨_,_,value,states,_⟩ := NKO_C08.occurrence wr rr merkle finish d pub proof ck hash pending weights reply entered
 have same : G pending weights=NJJ_Flush.output pending := Subtype.ext states
 rw [same]
 exact value.symm
#print axioms at_actual
end NLB_NativeFlush
