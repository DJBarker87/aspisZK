import R1Z.PV_OWND_InitialCheck
set_option autoImplicit false
namespace R1Z.PV_OWND_InitialDrop
open PV_OWN_Heap PV_OWN_Operations PV_OWNC_Vector PV_OWN_Link PV_W_Threading
/-- The modeled POD Vec error cleanup consumes the owner slot first, then frees
capacity bytes with the original layout. It never frees only len bytes. -/
theorem complete {S X E : Type}
 (dealloc : Nat → Request → S → Outcome E Unit × S) (b : Buffer Link) (w : State S X)
 (owned:w.memory.slots b.owner=some b.token) (nonzero:b.cell.size≠0) :
 dropOwned b.owner (fun _=>dropVecPod dealloc b.token b.cell) w=
 let after:={w with memory:=take b.owner w.memory}
 let result:=dealloc b.token.address ⟨b.cell.size,b.cell.alignment⟩ after.allocator
 ⟨result.1,{after with allocator:=result.2,memory:=retire b.token b.cell after.memory},
  [(after,.deallocate b.token.address b.cell.size b.cell.alignment)]⟩ := by
 simp only [dropOwned,owned,dropVecPod,nonzero,ite_false,free,emit]
#print axioms complete
end R1Z.PV_OWND_InitialDrop
