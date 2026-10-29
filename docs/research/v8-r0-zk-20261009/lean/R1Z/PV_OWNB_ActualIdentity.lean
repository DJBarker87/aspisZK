import R1Z.PV_OWNB_ActualFold
set_option autoImplicit false
namespace R1Z.PV_OWNB_ActualIdentity
open PV_OWNB_Cursor PV_OWN_Link PV_OWN_Bytes

theorem step_generation (keep : Link → Bool) (bytes : Nat → Link → Bytes) (q : Cursor) :
 (PV_OWNB_ActualFilter.step keep bytes q).token=q.token ∧
 (PV_OWNB_ActualFilter.step keep bytes q).memory.generations=q.memory.generations := by
 unfold PV_OWNB_ActualFilter.step
 split <;> exact ⟨rfl,rfl⟩

theorem generation (keep : Link → Bool) (bytes : Nat → Link → Bytes) (n : Nat) (q : Cursor) :
 (PV_OWNB_ActualFold.run keep bytes n q).token=q.token ∧
 (PV_OWNB_ActualFold.run keep bytes n q).memory.generations=q.memory.generations := by
 induction n generalizing q with
 | zero => exact ⟨rfl,rfl⟩
 | succ n ih =>
  rw [PV_OWNB_ActualFold.run]
  obtain ⟨ht,hg⟩:=ih (PV_OWNB_ActualFilter.step keep bytes q)
  obtain ⟨st,sg⟩:=step_generation keep bytes q
  exact ⟨ht.trans st,hg.trans sg⟩
#print axioms step_generation
#print axioms generation
end R1Z.PV_OWNB_ActualIdentity
