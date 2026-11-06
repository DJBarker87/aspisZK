import NIW_AlignRegularPostBoundary
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignRegularWindow
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl
variable [FIo_Native.Allocation]

def Slot (j : Nat) : Result NHM_RegularKinds.Reply → Prop
 | ok (_,_,parts) => epick parts j=NHI_Scalar.zero
 | _ => True

theorem zero_slot (c : Context) (before : Scratch)
 (domain : NIT_PairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value) (inv : NHX_RegularPost.Inv before initial)
 (j : Nat) (small : j<7)
 (outside : ∀ k∈NHM_RegularKinds.kinds (NGM_GuardExact.guard c.w.value 2#usize),j≠k.val) :
 Slot j (NIW_AlignRegularPhase.run c before).2.outcome := by
 have post := NIW_AlignRegularPostBoundary.source c before domain c0 c1 inv
 cases result : (NIW_AlignRegularPhase.run c before).2.outcome with
 | fail err => trivial
 | div => trivial
 | ok value =>
  rcases value with ⟨reply,after,parts⟩
  simp only [result,NIW_AlignRegularPostBoundary.Post] at post
  have frame := congrArg (fun x : Option E=>x.getD NHI_Scalar.zero) (post.2 j outside)
  change epick parts j=epick initial j at frame
  change epick parts j=NHI_Scalar.zero
  rw [frame]
  simp only [epick,initial,NIG_PairFrames.initial,Array.repeat,List.getElem?_replicate,small,ite_true,Option.getD_some]

theorem zero_and_four (c : Context) (before : Scratch)
 (domain : NIT_PairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value) (inv : NHX_RegularPost.Inv before initial) :
 Slot 0 (NIW_AlignRegularPhase.run c before).2.outcome ∧
 Slot 4 (NIW_AlignRegularPhase.run c before).2.outcome := by
 constructor
 · apply zero_slot c before domain c0 c1 inv 0 (by decide)
   intro k member
   have valid := NHM_RegularDomain.membership (NGM_GuardExact.guard c.w.value 2#usize) k member
   rcases valid with h|h|h|h|h <;> omega
 · apply zero_slot c before domain c0 c1 inv 4 (by decide)
   intro k member
   have valid := NHM_RegularDomain.membership (NGM_GuardExact.guard c.w.value 2#usize) k member
   rcases valid with h|h|h|h|h <;> omega

theorem scratch (c : Context) (before : Scratch)
 (domain : NIT_PairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value) (inv : NHX_RegularPost.Inv before initial) :
 match (NIW_AlignRegularPhase.run c before).2.outcome with
 | ok (_,after,_) => NHI_CellCanon.slice (alloc.vec.Vec.deref after) ∧ (alloc.vec.Vec.deref after).val.length=64
 | _ => True := by
 have post := NIW_AlignRegularPostBoundary.source c before domain c0 c1 inv
 cases result : (NIW_AlignRegularPhase.run c before).2.outcome with
 | fail err => trivial
 | div => trivial
 | ok value =>
  rcases value with ⟨reply,after,parts⟩
  simp only [result,NIW_AlignRegularPostBoundary.Post] at post
  exact ⟨post.1.1,post.1.2.1⟩

#print axioms zero_slot
#print axioms zero_and_four
#print axioms scratch
end AspisR1.NIW_AlignRegularWindow
