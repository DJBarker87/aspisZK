import R1Z.PV_OWNC_Unwind
set_option autoImplicit false
namespace R1Z.PV_OWNC_SourceIdentity
open PV_OWNB_Cursor PV_OWN_Link PV_OWNC_FoldSource PV_OWNC_SourceLoop
/-- The raw reader/write-sink loop never changes allocation identity, owner
slot or generations. Stores affect bytes only. -/
theorem step (keep : Link → Bool) (q : Cursor) :
 (sourceStep keep q).owner=q.owner ∧
 (sourceStep keep q).token=q.token ∧
 (sourceStep keep q).memory.slots=q.memory.slots ∧
 (sourceStep keep q).memory.generations=q.memory.generations := by
 unfold sourceStep
 dsimp only
 split <;> exact ⟨rfl,rfl,rfl,rfl⟩

theorem loop (keep : Link → Bool) (n : Nat) (q : Cursor) :
 (run keep n q).owner=q.owner ∧
 (run keep n q).token=q.token ∧
 (run keep n q).memory.slots=q.memory.slots ∧
 (run keep n q).memory.generations=q.memory.generations := by
 induction n generalizing q with
 | zero => exact ⟨rfl,rfl,rfl,rfl⟩
 | succ n ih =>
  have h:=ih (sourceStep keep q)
  have s:=step keep q
  exact ⟨h.1.trans s.1,h.2.1.trans s.2.1,h.2.2.1.trans s.2.2.1,h.2.2.2.trans s.2.2.2⟩
#print axioms step
#print axioms loop
end R1Z.PV_OWNC_SourceIdentity
