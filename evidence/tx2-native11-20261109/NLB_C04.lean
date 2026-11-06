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
theorem C04_step (proofArg : Slice U8) (p : verifier.Prepared) (root : Array U8 32#usize) (reply : R Unit)
 (entered : Event.merkle proofArg p root reply∈(run wr rr modelMerkle (finish fr) d pub proof ck hash none).events) (childProjection : nativeMerkle d proofArg p root 1#usize hash=modelMerkle d proofArg p root 1#usize hash) :
 window rr fr loc nativeResume nativeMerkle d hash (Event.merkle proofArg p root reply)=Event.merkle proofArg p root reply := by
 have call := NKE_CommonCalls.source wr rr modelMerkle (finish fr) d pub proof ck hash _ entered
 change reply=modelMerkle d proofArg p root 1#usize hash at call
 change Event.merkle proofArg p root (nativeMerkle d proofArg p root 1#usize hash)=_
 rw [childProjection,←call]
#print axioms C04_step
end NLB_Parent
