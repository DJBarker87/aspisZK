import NIT_TailCuts
import NIT_LowChain
import NIT_LibraChain
import NIT_PowersInstantiation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIT_TailLocal
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairComposition NIT_TailCuts

/-- Both CLOSED child laws are instantiated on the SAME owner/low/powers/extra.
The group return is the local observed arm; no enclosing pair success is assumed. -/
theorem local_log (w : Ref W) (f : Ref (Slice U8)) (low : Ref LowCells)
 (ap0 ap1 : Ref Powers) (parts : Parts)
 (s2 : w.value.variant=FIo_Native.transport.Variant.S2) (size : f.value.val.length=2048)
 (cl : canonical low.value) (c0 : canonical ap0.value) (c1 : canonical ap1.value)
 (ce : NHI_CellCanon.array w.value.extra) (cp : canonical parts) (group : E)
 (groupRun : FIo_Native.weights.grouped_inactive_pair w.value f.value low.value=ok group) :
 ∃ l after,groupCut w f low ap0 ap1 parts l after l.libra_reply ∧
 FIo_Native.weights.factored_s2_libra_weights ap0.value ap1.value w.value.extra=ok l.libra_reply ∧
 NHX_FactoredPacket.reference ap0.value ap1.value w.value.extra=ok l.libra_reply ∧
 NHM_GroupRoot.reference f.value low.value=ok l.group_reply ∧
 canonical after ∧ canonical l.libra_reply := by
 have cg := NHX_GroupPacket.output w.value f.value low.value s2 size cl group groupRun
 have groupModel : NHM_GroupRoot.reference f.value low.value=ok group := by
  rw [←NHX_GroupPacket.source w.value f.value low.value s2 size]
  exact groupRun
 obtain ⟨libra,factorRun,factorModel,canonical⟩ := NHX_FactoredPacket.source ap0.value ap1.value w.value.extra c0 c1 ce
 let l : Tail := ⟨w.address,f.address,2048,low.address,16,ap0.address,ap1.address,w.value.extra,group,libra,[0,1],2⟩
 let after := NIT_ArrayFrames.put parts 0 group
 have frame : ∀ k,k<7 → epick after k=if k=0 then group else epick parts k := by
  intro k _
  exact NIT_ArrayFrames.pick_put NHI_Scalar.zero parts 0 group (by decide) k
 have cut : groupCut w f low ap0 ap1 parts l after libra :=
  ⟨s2,size,cl,c0,c1,cp,cg,canonical,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,frame,rfl⟩
 have update := NIT_LowInterpretation.update_model parts 0#usize group (by decide)
 have ca := NHM_ArrayPreserve.canonical canonE parts after 0#usize group cp cg update
 exact ⟨l,after,cut,factorRun,factorModel,groupModel,ca,canonical⟩

/-- The native groupCut determines exactly the next parts array and opaque
factored reply; no extra frame or output-success condition is introduced. -/
theorem substituted (w : Ref W) (f : Ref (Slice U8)) (low : Ref LowCells)
 (ap0 ap1 : Ref Powers) (parts after : Parts) (l : Tail)
 (cut : groupCut w f low ap0 ap1 parts l after l.libra_reply)
 (ce : NHI_CellCanon.array w.value.extra)
 (groupRun : NHM_GroupRoot.reference f.value low.value=ok l.group_reply)
 (factorRun : NHX_FactoredPacket.reference ap0.value ap1.value w.value.extra=ok l.libra_reply) :
 (do let group ← FIo_Native.weights.grouped_inactive_pair w.value f.value low.value
     let updated ← Array.update parts 0#usize group
     let libra ← FIo_Native.weights.factored_s2_libra_weights ap0.value ap1.value w.value.extra
     ok (updated,libra))=ok (after,l.libra_reply) := by
 have frame := group_frame w f low ap0 ap1 parts l after l.libra_reply cut
 rcases cut with ⟨s2,size,_,c0,c1,_,_,_,_⟩
 have gr : FIo_Native.weights.grouped_inactive_pair w.value f.value low.value=ok l.group_reply := by
  rw [NHX_GroupPacket.source w.value f.value low.value s2 size]
  exact groupRun
 -- Extra canonicality is already supplied by the CLOSED factor law's source
 -- instantiation in local_log; this local substitution uses its exact reply.
 have factor : FIo_Native.weights.factored_s2_libra_weights ap0.value ap1.value w.value.extra=ok l.libra_reply := by
  obtain ⟨out,source,model,_⟩ := NHX_FactoredPacket.source ap0.value ap1.value w.value.extra c0 c1 ce
  have same := Result.ok.inj (model.symm.trans factorRun)
  simpa only [same] using source
 have update : Array.update parts 0#usize l.group_reply=ok after := by
  rw [frame]
  exact NIT_LowInterpretation.update_model parts 0#usize l.group_reply (by decide)
 simp only [gr,update,factor,bind_tc_ok]

#print axioms local_log
#print axioms substituted
end AspisR1.NIT_TailLocal
