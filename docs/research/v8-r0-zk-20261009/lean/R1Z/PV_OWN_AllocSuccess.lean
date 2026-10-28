import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem AllocSuccess (prim : Request → S → Outcome E (Option Nat) × S) (r : Request) (owner p : Nat)
 (w : State S X) (s : S) (h:prim r w.allocator=(.ok (some p),s)) :
 (allocate prim r owner w).world.memory.heap p=some (emptyCell r.size r.alignment owner) := by
 simp [allocate,emit,h,put]
#print axioms AllocSuccess
end R1Z.PV_OWN_Laws
