import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem AllocDisjoint (prim : Request → S → Outcome E (Option Nat) × S) (r : Request) (w : State S X)
 (p q : Nat) (s : S) (c : Cell) (adequate:AllocatorAdequate prim r w)
 (h:prim r w.allocator=(.ok (some p),s)) (old:w.memory.heap q=some c) (live:c.live=true) :
 q+c.size≤p ∨ p+r.size≤q := (adequate p s h).2.2.2 q c old live
#print axioms AllocDisjoint
end R1Z.PV_OWN_Laws
