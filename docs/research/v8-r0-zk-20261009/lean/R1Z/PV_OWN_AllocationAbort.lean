import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_AllocationAbort
open PV_W_Threading PV_OWN_Heap PV_OWN_Operations
/-- Actual handlers remain actions in the same world, not pure error values. -/
def request {S X E A : Type} (primitive : Request → S → Outcome E (Option Nat) × S)
 (r : Request) (owner : Nat) (abort : Action S X E A) (next : Token → Action S X E A) : Action S X E A :=
 bind (allocate primitive r owner) fun result =>
 match result with | none => abort | some token => next token

theorem null {S X E A : Type} (primitive : Request → S → Outcome E (Option Nat) × S)
 (r : Request) (owner : Nat) (abort : Action S X E A) (next : Token → Action S X E A)
 (w : State S X) (s : S) (h:primitive r w.allocator=(.ok none,s)) :
 request primitive r owner abort next w=
 ⟨(abort {w with allocator := s}).outcome,(abort {w with allocator := s}).world,
  [(w,.allocate r.size r.alignment)]++(abort {w with allocator := s}).calls⟩ := by
 simp [request,bind,allocate,emit,h]

theorem divergence {S X E A : Type} (primitive : Request → S → Outcome E (Option Nat) × S)
 (r : Request) (owner : Nat) (abort : Action S X E A) (next : Token → Action S X E A)
 (w : State S X) (s : S) (h:primitive r w.allocator=(.div,s)) :
 request primitive r owner abort next w=
 ⟨.div,{w with allocator := s},[(w,.allocate r.size r.alignment)]⟩ := by
 simp [request,bind,allocate,emit,h]
#print axioms null
#print axioms divergence
end R1Z.PV_OWN_AllocationAbort
