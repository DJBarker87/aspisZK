import NLZ_Resources
set_option autoImplicit false
namespace AspisR1.NMP_RejectionResources
open Aeneas Aeneas.Std
/-- A classifier supplied from the source Result shape, not an arbitrary native
success premise. Inner Rust Err values are returned source values but carry no
post-abort heap, just as outer failures/divergence carry none. -/
inductive Terminal (α : Type) (reject : α → Prop) where
 | accepted (value : α) (heap : NLZ_Resources.Heap) (live : ¬ reject value)
 | rejected (value : α) (stopped : reject value)
 | failed (error : Error)
 | diverged
def value {α : Type} {reject : α → Prop} : Terminal α reject → Result α
 | .accepted a _ _ => .ok a
 | .rejected a _ => .ok a
 | .failed e => .fail e
 | .diverged => .div
def finalHeap {α : Type} {reject : α → Prop} : Terminal α reject → Option NLZ_Resources.Heap
 | .accepted _ h _ => some h
 | .rejected _ _ => none
 | .failed _ => none
 | .diverged => none
/-- A typed inner rejection NEVER manufactures a final resource state. The
same actual error value is retained by value, rather than mapped to panic. -/
theorem rejection_no_heap {α : Type} {reject : α → Prop}
 (out : Terminal α reject) (a : α) (same : value out=.ok a)
 (stopped : reject a) : finalHeap out=none := by
 cases out with
 | accepted b h live =>
  have eq : b=a := by cases same;rfl
  exact False.elim (live (eq.symm ▸ stopped))
 | rejected b proof => rfl
 | failed e => cases same
 | diverged => cases same
/-- Any reported final heap belongs to a non-rejecting return. -/
theorem heap_is_live {α : Type} {reject : α → Prop}
 (out : Terminal α reject) (h : NLZ_Resources.Heap)
 (same : finalHeap out=some h) : ∃ a, value out=.ok a ∧ ¬reject a := by
 cases out with
 | accepted a heap live => exact ⟨a,rfl,live⟩
 | rejected a proof => cases same
 | failed e => cases same
 | diverged => cases same
#print axioms rejection_no_heap
#print axioms heap_is_live
end AspisR1.NMP_RejectionResources
