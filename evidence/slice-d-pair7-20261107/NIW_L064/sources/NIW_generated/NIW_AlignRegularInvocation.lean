import NIW_AlignRegularExecution
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignRegularInvocation
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl NIW_AlignRegularStream NIW_AlignRegularExecution
variable [FIo_Native.Allocation]

/-- The actual source execution determines the constructor witnesses in order.
No record, post-state or successful endpoint is selected from a model. -/
theorem ordered (w : W) (alpha : Slice E) (f : Slice U8) (ap0 ap1 : Powers)
 (ks : List Usize) (s : Scratch) (p : Parts) :
 Ordered ks s p (execute w alpha f ap0 ap1 ks s p).2
  (execute w alpha f ap0 ap1 ks s p).1 := by
 induction ks generalizing s p with
 | nil => exact .done s p
 | cons k ks ih =>
  cases call : FIo_Native.weights.process_kind w k alpha f 2#usize 64#usize ap0 ap1 s p with
  | fail e => simpa only [execute,call] using Ordered.failed k ks s p e
  | div => simpa only [execute,call] using Ordered.diverged k ks s p
  | ok value =>
   rcases value with ⟨reply,after,post⟩
   cases reply with
   | Err e => simpa only [execute,call] using Ordered.rejected k ks s after p post e
   | Ok u =>
    cases u
    simpa only [execute,call] using Ordered.continued k ks s after p post
     (execute w alpha f ap0 ap1 ks after post).2
     (execute w alpha f ap0 ap1 ks after post).1 (ih after post)

/-- Every clause of this invocation is discharged with the CLOSED row at the
recorded SAME arguments. No clause is a hypothesis of this theorem. -/
theorem clauses (w : W) (alpha : Slice E) (f : Slice U8) (ap0 ap1 : Powers)
 (s2 : w.variant=FIo_Native.transport.Variant.S2)
 (ks : List Usize) (s : Scratch) (p : Parts) :
 ∀ event∈(execute w alpha f ap0 ap1 ks s p).2,Clause w f ap0 ap1 event := by
 induction ks generalizing s p with
 | nil => intro event member;cases member
 | cons k ks ih =>
  have closed := NIW_AlignRegularStream.closed_clause w alpha f ap0 ap1 k s p s2
  cases call : FIo_Native.weights.process_kind w k alpha f 2#usize 64#usize ap0 ap1 s p with
  | fail e =>
   simp only [execute,call,List.mem_singleton]
   intro event same
   subst event
   simpa only [call] using closed
  | div =>
   simp only [execute,call,List.mem_singleton]
   intro event same
   subst event
   simpa only [call] using closed
  | ok value =>
   rcases value with ⟨reply,after,post⟩
   cases reply with
   | Err e =>
    simp only [execute,call,List.mem_singleton]
    intro event same
    subst event
    simpa only [call] using closed
   | Ok u =>
    cases u
    simp only [execute,call,List.mem_cons]
    intro event member
    rcases member with same | later
    · subst event;simpa only [call] using closed
    · exact ih after post event later

#print axioms ordered
#print axioms clauses
end AspisR1.NIW_AlignRegularInvocation
