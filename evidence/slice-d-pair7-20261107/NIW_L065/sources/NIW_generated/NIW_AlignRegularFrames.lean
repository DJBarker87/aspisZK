import NIW_AlignRegularInvocation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignRegularFrames
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl NIW_AlignRegularStream NIW_AlignRegularExecution
variable [FIo_Native.Allocation]

def Frame (event : Event) : Prop :=
 NHX_RegularPost.Inv event.before event.parts ∧
 match event.outcome with
 | ok (_,after,post) => NHX_RegularPost.Inv after post ∧
   ∀ j,j≠event.kind.val → post.val[j]?=event.parts.val[j]?
 | fail _ => True
 | div => True

theorem step (w : W) (alpha : Slice E) (f : Slice U8) (ap0 ap1 : Powers)
 (s2 : w.variant=FIo_Native.transport.Variant.S2)
 (hf : NHI_TensorOuterStep.Factors w) (c0 : canonical ap0) (c1 : canonical ap1)
 (k : Usize) (valid : NHX_RegularPost.Valid k) (s : Scratch) (p : Parts)
 (inv : NHX_RegularPost.Inv s p) :
 Frame ⟨k,s,p,FIo_Native.weights.process_kind w k alpha f 2#usize 64#usize ap0 ap1 s p⟩ := by
 refine ⟨inv,?_⟩
 cases call : FIo_Native.weights.process_kind w k alpha f 2#usize 64#usize ap0 ap1 s p with
 | fail e => trivial
 | div => trivial
 | ok value =>
  rcases value with ⟨reply,after,post⟩
  have refcall := (NHX_ProcessReference.source w k alpha f ap0 ap1 s p s2).symm.trans call
  have h := NHX_ProcessPost.post w k f ap0 ap1 s after p post reply valid hf c0 c1
   inv.1 inv.2.1 inv.2.2 refcall
  exact ⟨⟨h.1,h.2.1,h.2.2.1⟩,h.2.2.2⟩

/-- Every entered source event has the caller-established invariant; returning
Err retains its actual writes and full outside-kind frame. There are no facts
about any unentered suffix. No call-result clause is retained as a premise. -/
theorem all (w : W) (alpha : Slice E) (f : Slice U8) (ap0 ap1 : Powers)
 (s2 : w.variant=FIo_Native.transport.Variant.S2)
 (hf : NHI_TensorOuterStep.Factors w) (c0 : canonical ap0) (c1 : canonical ap1)
 (ks : List Usize) (valid : ∀ k∈ks,NHX_RegularPost.Valid k)
 (s : Scratch) (p : Parts) (inv : NHX_RegularPost.Inv s p) :
 ∀ event∈(execute w alpha f ap0 ap1 ks s p).2,Frame event := by
 induction ks generalizing s p with
 | nil => intro event member;cases member
 | cons k ks ih =>
  have head := step w alpha f ap0 ap1 s2 hf c0 c1 k (valid k (by simp)) s p inv
  have rest : ∀ k∈ks,NHX_RegularPost.Valid k := fun j hj=>valid j (by simp [hj])
  cases call : FIo_Native.weights.process_kind w k alpha f 2#usize 64#usize ap0 ap1 s p with
  | fail e =>
   simp only [execute,call,List.mem_singleton]
   intro event same;subst event;simpa only [call] using head
  | div =>
   simp only [execute,call,List.mem_singleton]
   intro event same;subst event;simpa only [call] using head
  | ok value =>
   rcases value with ⟨reply,after,post⟩
   cases reply with
   | Err e =>
    simp only [execute,call,List.mem_singleton]
    intro event same;subst event;simpa only [call] using head
   | Ok u =>
    cases u
    have next : NHX_RegularPost.Inv after post := by
     simpa only [Frame,call] using head.2.1
    simp only [execute,call,List.mem_cons]
    intro event member
    rcases member with same | later
    · subst event;simpa only [call] using head
    · exact ih rest after post next event later

#print axioms step
#print axioms all
end AspisR1.NIW_AlignRegularFrames
