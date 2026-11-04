import NFB_PhysicalFrame
import NFB_ResizeTrace
set_option autoImplicit false
namespace NFB_CollectorTrace
open Aeneas.Std

/-- Only initialized live payload is exposed. Publication remains zero until
SetLenOnDrop finishes; this models the pinned TrustedLen specialization. -/
structure Guard (A : Type) where
 initialized : List A
 published : Nat
 deriving Repr

def store {A : Type} (s : Guard A) (x : A) : Guard A :=
 ⟨s.initialized++[x],s.published⟩
def finish {A : Type} (s : Guard A) : Guard A :=
 ⟨s.initialized,s.initialized.length⟩
def fill {A : Type} : List A → Guard A → Guard A
 | [],s => s
 | x::xs,s => fill xs (store s x)

theorem stores {A : Type} (xs : List A) (s : Guard A) :
 (fill xs s).initialized=s.initialized++xs ∧ (fill xs s).published=s.published := by
 induction xs generalizing s with
 | nil => simp [fill]
 | cons x xs ih =>
  have h := ih (store s x)
  simpa [fill,store,List.append_assoc] using h

theorem complete {A : Type} (xs : List A) :
 finish (fill xs (⟨[],0⟩ : Guard A))=⟨xs,xs.length⟩ := by
 have h:=stores xs (⟨[],0⟩ : Guard A)
 simp only [List.nil_append] at h
 simp only [finish,h.1]

/-- Arbitrary old live windows and the new slot reconstruct one SAME-buffer
store. This law is shared by array initialization and row collection. -/
theorem window_step {A : Type} (before after : List A) (value : A)
 (size : after.length=before.length+1)
 (old : ∀ j,j<before.length → after[j]?=before[j]?)
 (new : after[before.length]?=some value) : after=before++[value] := by
 apply List.ext_getElem?
 intro j
 by_cases active : j<before.length
 · rw [old j active,List.getElem?_append_left active]
 · by_cases last : j=before.length
   · subst j
     rw [new,List.getElem?_append_right (by omega)]
     simp only [Nat.sub_self,List.getElem?_cons_zero]
   · rw [List.getElem?_eq_none (by omega : after.length≤j),
       List.getElem?_eq_none (by simp only [List.length_append,List.length_singleton];omega)]

inductive Trace {A : Type} : List A → Guard A → Guard A → Prop where
 | done (s : Guard A) : Trace [] s s
 | step (x : A) (xs : List A) (s next out : Guard A)
  (size : next.initialized.length=s.initialized.length+1)
  (old : ∀ j,j<s.initialized.length → next.initialized[j]?=s.initialized[j]?)
  (new : next.initialized[s.initialized.length]?=some x)
  (unpublished : next.published=s.published)
  (tail : Trace xs next out) : Trace (x::xs) s out

theorem meaning {A : Type} {xs : List A} {before after : Guard A}
 (trace : Trace xs before after) : after=fill xs before := by
 induction trace with
 | done => rfl
 | step x xs s next out size old new unpublished tail ih =>
  have h:=window_step s.initialized next.initialized x size old new
  have same : next=store s x := by cases next;cases s;simp_all [store]
  rw [ih,same]
  rfl
#print axioms stores
#print axioms complete
#print axioms window_step
#print axioms meaning
end NFB_CollectorTrace
