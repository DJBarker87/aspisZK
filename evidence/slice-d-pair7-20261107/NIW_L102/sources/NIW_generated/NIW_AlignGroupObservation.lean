import NIW_AlignFactoredReply
import NIT_PairControl
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignGroupObservation
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_TailCuts

def afterGroup (w : Ref W) (f : Ref (Slice U8)) (low : Ref LowCells)
 (ap0 ap1 : Ref Powers) (parts : Parts) (group : E) : Result (Parts×Powers×Tail) := do
 let after←Array.update parts 0#usize group
 let weights←FIo_Native.weights.factored_s2_libra_weights ap0.value ap1.value w.value.extra
 ok (after,weights,⟨w.address,f.address,2048,low.address,16,ap0.address,ap1.address,
  w.value.extra,group,weights,[0,1],2⟩)

theorem returned (w : Ref W) (f : Ref (Slice U8)) (low : Ref LowCells)
 (ap0 ap1 : Ref Powers) (parts : Parts)
 (s2 : w.value.variant=FIo_Native.transport.Variant.S2) (size : f.value.val.length=2048)
 (cl : canonical low.value) (c0 : canonical ap0.value) (c1 : canonical ap1.value)
 (ce : NHI_CellCanon.array w.value.extra) (cp : canonical parts)
 (group : E) (groupCall : FIo_Native.weights.grouped_inactive_pair w.value f.value low.value=ok group) :
 NIW_AlignFieldReply.Produced (afterGroup w f low ap0 ap1 parts group) (fun result=>
  groupCut w f low ap0 ap1 parts result.2.2 result.1 result.2.1 ∧ canonical result.1 ∧
  canonical result.2.1 ∧ NHM_GroupRoot.reference f.value low.value=ok result.2.2.group_reply ∧
  NHX_FactoredPacket.reference ap0.value ap1.value w.value.extra=ok result.2.2.libra_reply) := by
 have cg := NHX_GroupPacket.output w.value f.value low.value s2 size cl group groupCall
 have groupModel : NHM_GroupRoot.reference f.value low.value=ok group :=
  (NHX_GroupPacket.source w.value f.value low.value s2 size).symm.trans groupCall
 have factor := NIW_AlignFactoredReply.source ap0.value ap1.value w.value.extra c0 c1 ce
 cases call : FIo_Native.weights.factored_s2_libra_weights ap0.value ap1.value w.value.extra with
 | fail err => simp only [call,NIW_AlignFieldReply.Produced] at factor
 | div => simp only [call,NIW_AlignFieldReply.Produced] at factor
 | ok weights =>
  have cw := factor.2
  simp only [call,NIW_AlignFieldReply.Produced] at cw
  have model : NHX_FactoredPacket.reference ap0.value ap1.value w.value.extra=ok weights :=
   factor.1.symm.trans call
  have update := NIT_LowInterpretation.update_model parts 0#usize group (by decide)
  have frame : ∀ k,k<7 → epick (NIT_ArrayFrames.put parts 0 group) k=
   if k=0 then group else epick parts k := by
   intro k hk
   exact NIT_ArrayFrames.pick_put NHI_Scalar.zero parts 0 group (by decide) k
  have ca := NHM_ArrayPreserve.canonical canonE parts _ 0#usize group cp cg update
  unfold afterGroup
  rw [update,bind_tc_ok,call,bind_tc_ok]
  exact ⟨⟨s2,size,cl,c0,c1,cp,cg,cw,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,frame,rfl⟩,
   ca,cw,groupModel,model⟩

#print axioms returned
end AspisR1.NIW_AlignGroupObservation
