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
theorem C02_step (gamma : aspis_core.field.wide_exact.WideExact)
 (reply : Result (Array aspis_core.field.wide_exact.WideExact 29#usize))
 (entered : Event.powers gamma reply∈(run wr rr modelMerkle (finish fr) d pub proof ck hash none).events) :
 window rr fr loc nativeResume nativeMerkle d hash (Event.powers gamma reply)=Event.powers gamma reply := by
 have call := NKE_CommonCalls.source wr rr modelMerkle (finish fr) d pub proof ck hash _ entered
 change reply=NHT_PacketOps.powers 29#usize gamma at call
 change Event.powers gamma (NHT_PacketOps.powers 29#usize gamma)=_
 rw [←call]
#print axioms C02_step
end NLB_Parent
