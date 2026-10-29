import R1Z.PV_OWNB_CleanupConsumed
set_option autoImplicit false
namespace R1Z.PV_OWNB_NoDoubleCleanup
open PV_OWNB_Cursor PV_OWN_Heap PV_OWN_Operations PV_W_Threading

theorem no_second_call {S X E : Type} (dealloc : Nat → Request → S → Outcome E Unit × S)
 (q : Cursor) (h:PV_OWNB_Cursor.Valid q) (s : S) (x : X) :
 let first:=PV_OWNB_CursorCleanup.cleanup dealloc q ⟨q.memory,s,x⟩
 (PV_OWNB_CursorCleanup.cleanup dealloc q first.world).calls=[] := by
 have consumed:=PV_OWNB_CleanupConsumed.consumed dealloc q h s x
 have empty (w : State S X) (hz:w.memory.slots q.owner=none) :
  (PV_OWNB_CursorCleanup.cleanup dealloc q w).calls=[] := by
  simp [PV_OWNB_CursorCleanup.cleanup,dropOwned,hz]
 exact empty _ consumed
#print axioms no_second_call
end R1Z.PV_OWNB_NoDoubleCleanup
