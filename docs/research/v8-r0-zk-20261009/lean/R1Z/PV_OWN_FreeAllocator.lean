import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Laws
open PV_OWN_Heap PV_OWN_Bytes PV_OWN_View PV_OWN_Operations PV_W_Threading
variable {S X E T : Type}
theorem FreeAllocator (prim : Nat → Request → S → Outcome E Unit × S) (t : Token) (c : Cell) (w : State S X) :
 (free prim t c w).world.allocator=(prim t.address ⟨c.size,c.alignment⟩ w.allocator).2 := rfl
#print axioms FreeAllocator
end R1Z.PV_OWN_Laws
