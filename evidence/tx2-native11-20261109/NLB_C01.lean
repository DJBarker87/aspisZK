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
theorem C01_step (checkpoint proofArg publicArg : Slice U8) (reply : R (verifier.Prepared × verifier.Accumulator))
 (entered : Event.resume checkpoint proofArg publicArg reply∈(run wr rr modelMerkle (finish fr) d pub proof ck hash none).events) (childProjection : nativeResume d checkpoint proofArg publicArg hash=
   NJJ_Common.resume wr d checkpoint proofArg publicArg .S2 hash) :
 window rr fr loc nativeResume nativeMerkle d hash (Event.resume checkpoint proofArg publicArg reply)=Event.resume checkpoint proofArg publicArg reply := by
 have call := NKE_CommonCalls.source wr rr modelMerkle (finish fr) d pub proof ck hash _ entered
 change reply=NJJ_Common.resume wr d checkpoint proofArg publicArg .S2 hash at call
 change Event.resume checkpoint proofArg publicArg (nativeResume d checkpoint proofArg publicArg hash)=_
 rw [childProjection,←call]
#print axioms C01_step
end NLB_Parent
