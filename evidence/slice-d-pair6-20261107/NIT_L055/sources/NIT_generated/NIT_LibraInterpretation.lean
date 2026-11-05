import NIT_LowInterpretation
import NIT_FinalCompleteness
set_option autoImplicit false
namespace AspisR1.NIT_LibraInterpretation
open Aeneas Aeneas.Std Result ControlFlow LPi_FieldValues NIT_Cuts NIT_FieldInterpretation NIT_PairComposition

/-- The field read, product and sum are associated at the SAME f/j/parts4 cut. -/
theorem window (f : Ref (Slice U8)) (libra : Powers) (j : Usize)
 (before after : Parts) (l : LibraLog) (cut : cutLibraLog f libra j.val before l after)
 (fieldLaw : FIo_Native.weights.field f.value j=ok l.coefficient)
 (mulLaw : EMul l.mul_a l.mul_b l.product) (addLaw : EAdd l.add_a l.add_b l.reply) :
 NIG_LibraLoop.window f.value libra j before=ok after ∧ canonical after := by
 have frame := libra_frame f libra j.val before after l cut
 rcases cut with ⟨small,_,cl,cb,cc,_,_,_,_,_,_,_,ma,mb,aa,ab,_⟩
 have cm := em l.mul_a l.mul_b l.product (ma.symm ▸ cc)
  (mb.symm ▸ epick_canonical libra cl j.val) mulLaw
 have ca := ea l.add_a l.add_b l.reply (aa.symm ▸ epick_canonical before cb 4)
  (ab.symm ▸ cm.2) addLaw
 rw [ma,mb] at cm
 rw [aa,ab] at ca
 have update : Array.update before 4#usize l.reply=ok after := by
  rw [frame]
  exact NIT_LowInterpretation.update_model before 4#usize l.reply (by decide)
 refine ⟨?_,NHM_ArrayPreserve.canonical canonE before after 4#usize l.reply cb ca.2 update⟩
 simp only [NIG_LibraLoop.window,epick_index before 4#usize (by decide),fieldLaw,
  epick_index libra j small,cm.1,bind_tc_ok]
 change (do let value ← FIo_Native.aspis_core.field.wide_exact.WideExact.add (epick before 4) l.product;Array.update before 4#usize value)=ok after
 rw [ca.1]
 exact update

/-- Returning local logs are constructed from CLOSED callees; an aborting field
call is handled by the separate prefix constructors, never encoded as Rust Err. -/
theorem local_log (f : Ref (Slice U8)) (size : f.value.val.length=2048)
 (libra : Powers) (cl : canonical libra) (j : Usize) (small : j.val<4)
 (before : Parts) (cb : canonical before) (coefficient : E)
 (fieldLaw : FIo_Native.weights.field f.value j=ok coefficient) :
 ∃ l after,cutLibraLog f libra j.val before l after ∧
 l.coefficient=coefficient ∧ EMul l.mul_a l.mul_b l.product ∧
 EAdd l.add_a l.add_b l.reply ∧ canonical after := by
 have cc := NHE_FieldCanonical.success f.value j (by omega) coefficient fieldLaw
 let weight := epick libra j.val
 let old := epick before 4
 obtain ⟨product,hm,cp,vm⟩ := LPi_TowerValues.wide_mul coefficient weight cc
  (epick_canonical libra cl j.val)
 obtain ⟨reply,ha,ca,va⟩ := NIT_FinalCompleteness.add_complete old product
  (epick_canonical before cb 4) cp
 let l : LibraLog := ⟨f.address,2048,j.val,coefficient,coefficient,weight,product,old,product,reply,3,[0,1,2]⟩
 let after := NIT_ArrayFrames.put before 4 reply
 have frame : ∀ k,k<7 → epick after k=if k=4 then reply else epick before k := by
  intro k _
  exact NIT_ArrayFrames.pick_put NHI_Scalar.zero before 4 reply (by decide) k
 have cut : cutLibraLog f libra j.val before l after :=
  ⟨small,size,cl,cb,cc,cp,ca,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,frame⟩
 have result := window f libra j before after l cut fieldLaw vm va
 exact ⟨l,after,cut,rfl,vm,va,result.2⟩

theorem step (f : Ref (Slice U8)) (libra : Powers) (s : NIG_LibraLoop.State)
 (after : Parts) (l : LibraLog) (cut : cutLibraLog f libra s.1.start.val s.2 l after)
 (fieldLaw : FIo_Native.weights.field f.value s.1.start=ok l.coefficient)
 (mulLaw : EMul l.mul_a l.mul_b l.product) (addLaw : EAdd l.add_a l.add_b l.reply)
 (last : s.1.end.val=4) :
 ∃ rest,NIG_LibraLoop.body f.value libra s=ok (.cont (rest,after)) ∧
 core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1=ok (some s.1.start,rest) ∧
 rest.end.val=4 ∧ rest.start.val=s.1.start.val+1 ∧ canonical after := by
 have small := cut.1
 obtain ⟨rest,next,inc,he⟩ := NHI_ForwardRange.active s.1 (by omega)
 have cell := window f libra s.1.start s.2 after l cut fieldLaw mulLaw addLaw
 refine ⟨rest,?_,next,by rw [he];exact last,inc,cell.2⟩
 simp only [NIG_LibraLoop.body,next,bind_tc_ok]
 dsimp! only
 simp only [cell.1,bind_tc_ok]

#print axioms window
#print axioms local_log
#print axioms step
end AspisR1.NIT_LibraInterpretation
