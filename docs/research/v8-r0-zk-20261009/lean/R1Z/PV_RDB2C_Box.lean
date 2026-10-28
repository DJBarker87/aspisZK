import R1Z.PV_RDB2C_PublicRequests
namespace R1Z.PV_RDB2C_Box
open PV_RDB2C_PublicRequests
structure World (T S : Type) where
  allocator : S
  objects : Nat → Option T
  requests : List Request
  live : Nat → Bool
inductive Outcome (T : Type) where
  | allocationAbort
  | returned (pointer : Nat) (value : T)

/-- Explicit typed allocation followed by initialization. Failure has the
allocator's post-state and request, with no initialized object fabricated. -/
def lowered {T S : Type} (allocate : Request → S → Option Nat × S)
    (request : Request) (value : T) (w : World T S) : Outcome T × World T S :=
  let (pointer,state) := allocate request w.allocator
  let after := {w with allocator := state,requests := w.requests++[request]}
  match pointer with
  | none => (.allocationAbort,after)
  | some p => (.returned p value,
      {after with objects := fun a => if a=p then some value else w.objects a,
                  live := fun a => if a=p then true else w.live a})

/-- Owned allocate-uninitialized/write/assume-init reference, complete on null.
The compiler's box_new-to-this-sequence association is separately required. -/
def reference {T S : Type} (allocate : Request → S → Option Nat × S)
    (request : Request) (value : T) (w : World T S) : Outcome T × World T S :=
  match allocate request w.allocator with
  | (none,state) => (.allocationAbort,{w with allocator := state,requests := w.requests++[request]})
  | (some p,state) => (.returned p value,
      {allocator := state, requests := w.requests++[request],
       objects := fun a => if a=p then some value else w.objects a,
       live := fun a => if a=p then true else w.live a})

theorem complete {T S : Type} (allocate : Request → S → Option Nat × S)
    (request : Request) (value : T) (w : World T S) :
    lowered allocate request value w=reference allocate request value w := by
  unfold lowered reference
  cases allocate request w.allocator with
  | mk p s => cases p <;> rfl

theorem allocation_failure {T S : Type} (allocate : Request → S → Option Nat × S)
    (request : Request) (value : T) (w : World T S) (state : S)
    (h : allocate request w.allocator=(none,state)) :
    lowered allocate request value w =
      (.allocationAbort,{w with allocator := state, requests := w.requests++[request]}) := by
  simp only [lowered,h]

theorem initialized {T S : Type} (allocate : Request → S → Option Nat × S)
    (request : Request) (value : T) (w : World T S) (p : Nat) (state : S)
    (h : allocate request w.allocator=(some p,state)) :
    (lowered allocate request value w).2.objects p=some value ∧
    (lowered allocate request value w).2.live p=true := by simp [lowered,h]

theorem frame {T S : Type} (allocate : Request → S → Option Nat × S)
    (request : Request) (value : T) (w : World T S) (p a : Nat) (state : S)
    (h : allocate request w.allocator=(some p,state)) (different : a≠p) :
    (lowered allocate request value w).2.objects a=w.objects a ∧
    (lowered allocate request value w).2.live a=w.live a := by simp [lowered,h,different]

/-- Freshness is explicitly the retained runtime/allocator primitive adequacy
law. This theorem does not prove that an arbitrary allocate callback is fresh. -/
theorem fresh_under_primitive_adequacy {T S : Type}
    (allocate : Request → S → Option Nat × S) (request : Request) (value : T)
    (w : World T S) (p : Nat) (state : S)
    (adequacy : ∀ p state, allocate request w.allocator=(some p,state) → w.live p=false)
    (h : allocate request w.allocator=(some p,state)) :
    w.live p=false ∧ (lowered allocate request value w).2.objects p=some value :=
  ⟨adequacy p state h,(initialized allocate request value w p state h).1⟩

#print axioms complete
#print axioms allocation_failure
#print axioms initialized
#print axioms frame
#print axioms fresh_under_primitive_adequacy
end R1Z.PV_RDB2C_Box
