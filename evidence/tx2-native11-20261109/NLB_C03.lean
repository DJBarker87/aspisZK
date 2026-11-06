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
theorem C03_step (bytes : Slice U8) (reply : Result (Option aspis_core.field.wide_exact.WideExact))
 (entered : Event.inactive bytes reply∈(run wr rr modelMerkle (finish fr) d pub proof ck hash none).events) :
 window rr fr loc nativeResume nativeMerkle d hash (Event.inactive bytes reply)=Event.inactive bytes reply := by
 have call := (NKO_C03.occurrence wr rr modelMerkle (finish fr) d pub proof ck hash bytes reply entered).2.2.2
 change Event.inactive bytes (NJC_ClosedCalls.inactive bytes)=_
 rw [←call]
#print axioms C03_step
end NLB_Parent
