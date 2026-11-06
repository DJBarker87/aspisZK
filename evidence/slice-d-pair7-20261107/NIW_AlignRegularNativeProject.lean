import NIW_AlignRegularNativeView
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignRegularNativeProject
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl NIW_AlignRegularNativeView
variable [FIo_Native.Allocation]

/-- Compatibility only for the returning branches on which project is defined.
Shared regular success intentionally remains outside this partial projection.
Nothing here asserts identity of an independent supplied raw native record. -/
theorem source (c : Context) (before : Scratch)
 (domain : NIT_PairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value) (inv : NHX_RegularPost.Inv before initial) :
 match project c before with
 | none => True
 | some view => NIW_AlignFrames.cutStream (NGM_GuardExact.guard c.w.value 2#usize)
   c.partsAddress view.stream view.scratch view.parts view.reply := by
 have post := NIW_AlignRegularPostBoundary.source c before domain c0 c1 inv
 cases outcome : (NIW_AlignRegularPhase.run c before).2.outcome with
 | fail err => simp only [project,outcome]
 | div => simp only [project,outcome]
 | ok value =>
  rcases value with ⟨reply,after,parts⟩
  simp only [outcome,NIW_AlignRegularPostBoundary.Post] at post
  cases reply with
  | Err err =>
   simp only [project,outcome]
   exact local_cut c _ (.Err err) after parts post.1 (Or.inr ⟨err,rfl⟩)
  | Ok unit =>
   cases unit
   cases guard : NGM_GuardExact.guard c.w.value 2#usize with
   | false =>
    simp only [project,outcome,guard,ite_false]
    exact local_cut c false (.Ok ()) after parts post.1 (Or.inl rfl)
   | true => simp only [project,outcome,guard,ite_true]

#print axioms source
end AspisR1.NIW_AlignRegularNativeProject
