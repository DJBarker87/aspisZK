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
theorem C09_step (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator) (reply : R Unit)
 (entered : Event.finish v p a reply∈(run wr rr modelMerkle (finish fr) d pub proof ck hash none).events) :
 window rr fr loc nativeResume nativeMerkle d hash (Event.finish v p a reply)=Event.finish v p a reply := by
 have call := NKE_CommonCalls.source wr rr modelMerkle (finish fr) d pub proof ck hash _ entered
 change reply=finish fr v p a none at call
 have child := (NKO_C09.child_at_actual wr rr modelMerkle (finish fr) d pub proof ck hash v p a reply entered fr loc).1
 change Event.finish v p a (NHT_ResultPort.action (NJF_FinishObserved.G fr loc v p a).1)=_
 rw [←child]
 exact congrArg (Event.finish v p a) call.symm
#print axioms C09_step
end NLB_Parent
