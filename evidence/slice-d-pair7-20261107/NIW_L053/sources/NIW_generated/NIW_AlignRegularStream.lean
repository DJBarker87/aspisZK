import NIW_AlignRegular
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignRegularStream
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl
variable [FIo_Native.Allocation]

/-- One entered call, with its complete observed outcome. Abort outcomes have
no invented mutable post: the stream ends at this event. -/
structure Event where
 kind : Usize
 before : Scratch
 parts : Parts
 outcome : Result NHM_RegularKinds.Reply

/-- Intermediate invocation relation, not a permitted root hypothesis. Each
clause is at the recorded SAME decoded arguments, never PairEdges' seed. -/
def Clause (w : W) (f : Slice U8) (ap0 ap1 : Powers) (e : Event) : Prop :=
 e.outcome=NIW_AlignRegular.child w f ap0 ap1 e.kind e.before e.parts

inductive Ordered : List Usize → Scratch → Parts → List Event → Result NHM_RegularKinds.Reply → Prop
 | done (s : Scratch) (p : Parts) : Ordered [] s p [] (ok (.Ok (),s,p))
 | failed (k : Usize) (ks : List Usize) (s : Scratch) (p : Parts) (e : Error) :
   Ordered (k::ks) s p [⟨k,s,p,fail e⟩] (fail e)
 | diverged (k : Usize) (ks : List Usize) (s : Scratch) (p : Parts) :
   Ordered (k::ks) s p [⟨k,s,p,div⟩] div
 | rejected (k : Usize) (ks : List Usize) (s after : Scratch) (p post : Parts)
   (e : FIo_Native.verifier.Error) :
   Ordered (k::ks) s p [⟨k,s,p,ok (.Err e,after,post)⟩] (ok (.Err e,after,post))
 | continued (k : Usize) (ks : List Usize) (s after : Scratch) (p post : Parts)
   (events : List Event) (out : Result NHM_RegularKinds.Reply)
   (tail : Ordered ks after post events out) :
   Ordered (k::ks) s p (⟨k,s,p,ok (.Ok (),after,post)⟩::events) out

/-- Fold the supplied chronological observations. The head's complete law is
used before recursing at its actual post-state; no new log is chosen. -/
theorem fold (w : W) (f : Slice U8) (ap0 ap1 : Powers)
 (ks : List Usize) (s : Scratch) (p : Parts) (events : List Event)
 (out : Result NHM_RegularKinds.Reply)
 (ordered : Ordered ks s p events out)
 (clauses : ∀ e∈events,Clause w f ap0 ap1 e) :
 NHM_RegularKinds.go (NIW_AlignRegular.child w f ap0 ap1) ks s p=out := by
 induction ordered with
 | done s p => rfl
 | failed k ks s p e =>
  have h := (clauses _ (by simp)).symm
  change NIW_AlignRegular.child w f ap0 ap1 k s p=fail e at h
  rw [NHM_RegularKinds.go,h];rfl
 | diverged k ks s p =>
  have h := (clauses _ (by simp)).symm
  change NIW_AlignRegular.child w f ap0 ap1 k s p=div at h
  rw [NHM_RegularKinds.go,h];rfl
 | rejected k ks s after p post e =>
  have h := (clauses _ (by simp)).symm
  change NIW_AlignRegular.child w f ap0 ap1 k s p=ok (.Err e,after,post) at h
  exact NHM_RegularKinds.first_error _ k ks s after p post e h
 | continued k ks s after p post events out tail ih =>
  have h := (clauses _ (by simp)).symm
  change NIW_AlignRegular.child w f ap0 ap1 k s p=ok (.Ok (),after,post) at h
  rw [NHM_RegularKinds.after_ok _ k ks s after p post h]
  exact ih (fun e member=>clauses e (by simp [member]))

/-- Child law discharge for every entered event, all Result arms. This has no
child equality hypothesis; the right side is the actual decoded CLOSED call. -/
theorem closed_clause (w : W) (alpha : Slice E) (f : Slice U8) (ap0 ap1 : Powers)
 (k : Usize) (s : Scratch) (p : Parts)
 (s2 : w.variant=FIo_Native.transport.Variant.S2) :
 Clause w f ap0 ap1 ⟨k,s,p,
  FIo_Native.weights.process_kind w k alpha f 2#usize 64#usize ap0 ap1 s p⟩ :=
 NHX_ProcessReference.source w k alpha f ap0 ap1 s p s2

#print axioms fold
#print axioms closed_clause
end AspisR1.NIW_AlignRegularStream
