import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem AllocFailure (prim : Request → S → Outcome E (Option Nat) × S) (r : Request) (owner : Nat)
 (w : State S X) (s : S) (e:E) (h:prim r w.allocator=(.fail e,s)) :
 (allocate prim r owner w).world={w with allocator := s} := by simp [allocate,emit,h]
#print axioms AllocFailure
end R1Z.PV_OWN_Laws
