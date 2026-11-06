import NLB_Windows
set_option autoImplicit false
noncomputable section
namespace NLB_Parent
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
variable (wr rr fr : NP6_StdModel.Reservation) (loc : NIW_AlignFinishComposed.Locations)
 (nativeResume : Resume) (nativeMerkle modelMerkle : Merkle)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)

/-- Auxiliary SAME-occurrence step; this is not a row root. C01/C04 take
only a child Result projection here, explicitly insufficient for a row packet. -/
theorem C07_step (proofArg : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
 (reply : R (verifier.Accumulator × verifier.BatchedWeights))
 (entered : Event.query proofArg p a g geometry pending reply∈(run wr rr modelMerkle (finish fr) d pub proof ck hash none).events) :
 window rr fr loc nativeResume nativeMerkle d hash (Event.query proofArg p a g geometry pending reply)=Event.query proofArg p a g geometry pending reply := by
 have call := NKE_CommonCalls.source wr rr modelMerkle (finish fr) d pub proof ck hash _ entered
 change reply=NJJ_Common.query proofArg p a g none geometry pending 22#usize at call
 change Event.query proofArg p a g geometry pending
   (NKO_QueryReturnG.G (NKE_QueryReturn.observed (NJJ_Common.query proofArg p a g none geometry pending 22#usize)))=_
 rw [NKO_QueryReturnG.retained_return,←call]
#print axioms C07_step
end NLB_Parent
