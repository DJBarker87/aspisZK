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
theorem C06_step (weights : Slice aspis_core.field.QM31) (reply : R verifier.BatchedWeights)
 (entered : Event.pending weights reply∈(run wr rr modelMerkle (finish fr) d pub proof ck hash none).events) :
 window rr fr loc nativeResume nativeMerkle d hash (Event.pending weights reply)=Event.pending weights reply := by
 have call := NKE_PendingAtSource.source wr rr modelMerkle (finish fr) d pub proof ck hash weights reply entered
 change Event.pending weights (NKE_CommonNative.pendingG rr weights)=_
 rw [←call]
#print axioms C06_step
end NLB_Parent
