import NNT_Port241
set_option autoImplicit false
noncomputable section
namespace NNT_RelReplay241
open RSL RSL.TX2_241 RSL.NNT NMS_R2Refine NMS_R2StepFacts NMS_R2Replay241
open NMX_R7_RelVerify241 NNS_Fold241

theorem relPacket_iff (R0 : Bytes → Bytes → Prop)
 (w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit)) :
 RelPacket (TAS.lib V0 R0 w) NMX_R8_RelReplay241.verify ↔ LawRefines V0 R0 w :=
 ⟨fun h x env o d r => h x d env o r, fun h x d env o r => h x env o d r⟩

theorem fold (R0 : Bytes → Bytes → Prop)
 (w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit))
 (a : Args) (domain : Domain (TAS.lib V0 R0 w) a) (h : LawRefines V0 R0 w) :
 Refines (NMX_R9_RelReplay241.replay a) (TX2_241.Ref L D (TAS.lib V0 R0 w) a) := by
 rw [NMS_R2Replay241.factor]
 unfold NMX_R9_RelReplay241.replay
 apply rsseq (refl _)
 apply rsbind_using (fun env o run => ⟨trivial,run⟩)
 intro env validated events execution
 have scope := NMS_R2Facts242.successful L D LIBB_PoolLib.scanner_extent _ env validated events execution
 rw [←NNS_LibraryContext.after_validate L V0 R0 w NMX_R8_RelReplay241.verify a validated]
 exact (NMX_R7_RelValidate241.fold L (TAS.lib V0 R0 w) NMX_R8_RelReplay241.verify
  ((relPacket_iff R0 w).mpr h) a domain validated scope) env
#print axioms relPacket_iff
#print axioms fold
end NNT_RelReplay241
