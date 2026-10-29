import R1Z.PV_OWNB_CursorCleanup
set_option autoImplicit false
namespace R1Z.PV_OWNB_CleanupRetired
open PV_OWNB_Cursor PV_OWN_Heap PV_OWN_Operations PV_W_Threading
/-- Retirement describes the inherited primitive model, not deallocator adequacy. -/
theorem dead {S X E : Type} (dealloc : Nat → Request → S → Outcome E Unit × S)
 (q : Cursor) (h:PV_OWNB_Cursor.Valid q) (s : S) (x : X) (nz:q.cell.size≠0) :
 let after:=(PV_OWNB_CursorCleanup.cleanup dealloc q ⟨q.memory,s,x⟩).world.memory
 ∀ c, after.heap q.token.address=some c → ¬Live after q.token c := by
 rw [PV_OWNB_CursorCleanup.gate dealloc q h s x]
 simp only [dropVecPod,nz,ite_false,free,emit]
 intro c hc hl
 have eq:c={q.cell with live:=false} := by
  simpa [retire,put] using hc.symm
 subst c
 have bad:=hl.2.1
 cases bad
#print axioms dead
end R1Z.PV_OWNB_CleanupRetired
