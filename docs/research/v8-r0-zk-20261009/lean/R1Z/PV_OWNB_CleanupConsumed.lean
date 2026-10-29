import R1Z.PV_OWNB_CursorCleanup
set_option autoImplicit false
namespace R1Z.PV_OWNB_CleanupConsumed
open PV_OWNB_Cursor PV_OWN_Heap PV_OWN_Operations PV_W_Threading

theorem consumed {S X E : Type} (dealloc : Nat → Request → S → Outcome E Unit × S)
 (q : Cursor) (h:PV_OWNB_Cursor.Valid q) (s : S) (x : X) :
 (PV_OWNB_CursorCleanup.cleanup dealloc q ⟨q.memory,s,x⟩).world.memory.slots q.owner=none := by
 rw [PV_OWNB_CursorCleanup.gate dealloc q h s x]
 by_cases hz:q.cell.size=0
 · simp [dropVecPod,hz,dropPod,lift,take]
 · simp [dropVecPod,hz,free,emit,retire,take]
#print axioms consumed
end R1Z.PV_OWNB_CleanupConsumed
