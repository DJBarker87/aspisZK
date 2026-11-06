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
theorem C08_step (pending : verifier.BatchedWeights) (weights : Slice aspis_core.field.QM31)
 (reply : Result (Slice aspis_core.field.QM31))
 (entered : Event.flush pending weights reply∈(run wr rr modelMerkle (finish fr) d pub proof ck hash none).events) :
 window rr fr loc nativeResume nativeMerkle d hash (Event.flush pending weights reply)=Event.flush pending weights reply := by
 have call := (NKO_C08.occurrence wr rr modelMerkle (finish fr) d pub proof ck hash pending weights reply entered).2.2.1
 change Event.flush pending weights (ok (NJJ_Flush.output pending))=_
 rw [←call]
#print axioms C08_step
end NLB_Parent
