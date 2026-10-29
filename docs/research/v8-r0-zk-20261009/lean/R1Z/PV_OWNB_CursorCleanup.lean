import R1Z.PV_OWNB_Cursor
set_option autoImplicit false
namespace R1Z.PV_OWNB_CursorCleanup
open PV_OWNB_Cursor PV_OWN_Heap PV_OWN_Operations PV_W_Threading
/-- POD prefix/tail glue is empty; allocation cleanup consumes the current owner. -/
def cleanup {S X E : Type} (dealloc : Nat → Request → S → Outcome E Unit × S)
 (q : Cursor) : Action S X E Unit :=
 dropOwned q.owner (fun t=>dropVecPod dealloc t q.cell)

theorem gate {S X E : Type} (dealloc : Nat → Request → S → Outcome E Unit × S)
 (q : Cursor) (h:PV_OWNB_Cursor.Valid q) (s : S) (x : X) :
 cleanup dealloc q ⟨q.memory,s,x⟩=
 dropVecPod dealloc q.token q.cell ⟨take q.owner q.memory,s,x⟩ := by
 unfold PV_OWNB_Cursor.Valid at h
 simp [cleanup,dropOwned,h.1.1.2.1]

theorem zero {S X E : Type} (dealloc : Nat → Request → S → Outcome E Unit × S)
 (q : Cursor) (h:PV_OWNB_Cursor.Valid q) (s : S) (x : X) (z:q.cell.size=0) :
 (cleanup dealloc q ⟨q.memory,s,x⟩).calls=[] := by
 rw [gate dealloc q h s x]
 simp [dropVecPod,z,dropPod,lift]

theorem positive {S X E : Type} (dealloc : Nat → Request → S → Outcome E Unit × S)
 (q : Cursor) (h:PV_OWNB_Cursor.Valid q) (s : S) (x : X) (nz:q.cell.size≠0) :
 (cleanup dealloc q ⟨q.memory,s,x⟩).calls=
 [(⟨take q.owner q.memory,s,x⟩,.deallocate q.token.address q.cell.size q.cell.alignment)] := by
 rw [gate dealloc q h s x]
 simp [dropVecPod,nz,free,emit]
attribute [local irreducible] cleanup
#print axioms gate
#print axioms zero
#print axioms positive
end R1Z.PV_OWNB_CursorCleanup
