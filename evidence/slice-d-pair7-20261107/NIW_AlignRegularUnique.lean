import NIW_AlignRegularInvocation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignRegularUnique
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl NIW_AlignRegularStream NIW_AlignRegularExecution
variable [FIo_Native.Allocation]

/-- Reverse direction: a supplied source-ordered native stream, with its
internally discharged clauses, is the complete source observation stream.
This helper is not a root permitted to assume the clause producer. -/
theorem determined (w : W) (alpha : Slice E) (f : Slice U8) (ap0 ap1 : Powers)
 (s2 : w.variant=FIo_Native.transport.Variant.S2)
 (ks : List Usize) (s : Scratch) (p : Parts) (events : List Event)
 (out : Result NHM_RegularKinds.Reply)
 (ordered : Ordered ks s p events out)
 (clauses : ∀ e∈events,Clause w f ap0 ap1 e) :
 execute w alpha f ap0 ap1 ks s p=(out,events) := by
 induction ordered with
 | done s p => rfl
 | failed k ks s p err =>
  have law := clauses ⟨k,s,p,fail err⟩ (by simp)
  have call : FIo_Native.weights.process_kind w k alpha f 2#usize 64#usize ap0 ap1 s p=fail err :=
   (NHX_ProcessReference.source w k alpha f ap0 ap1 s p s2).trans law.symm
  simp only [execute,call]
 | diverged k ks s p =>
  have law := clauses ⟨k,s,p,div⟩ (by simp)
  have call : FIo_Native.weights.process_kind w k alpha f 2#usize 64#usize ap0 ap1 s p=div :=
   (NHX_ProcessReference.source w k alpha f ap0 ap1 s p s2).trans law.symm
  simp only [execute,call]
 | rejected k ks s after p post err =>
  have law := clauses ⟨k,s,p,ok (.Err err,after,post)⟩ (by simp)
  have call : FIo_Native.weights.process_kind w k alpha f 2#usize 64#usize ap0 ap1 s p=ok (.Err err,after,post) :=
   (NHX_ProcessReference.source w k alpha f ap0 ap1 s p s2).trans law.symm
  simp only [execute,call]
 | continued k ks s after p post events out tail ih =>
  have law := clauses ⟨k,s,p,ok (.Ok (),after,post)⟩ (by simp)
  have call : FIo_Native.weights.process_kind w k alpha f 2#usize 64#usize ap0 ap1 s p=ok (.Ok (),after,post) :=
   (NHX_ProcessReference.source w k alpha f ap0 ap1 s p s2).trans law.symm
  have rest := ih (fun e member=>clauses e (by simp [member]))
  simp only [execute,call,rest]

#print axioms determined
end AspisR1.NIW_AlignRegularUnique
