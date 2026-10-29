import R1Z.PV_OWNB_FilterFold
set_option autoImplicit false
namespace R1Z.PV_OWNB_FilterIdentity
open PV_OWNB_Cursor PV_OWN_Link

theorem source (keep : Link → Bool) (n : Nat) (q : Cursor) :
 (PV_OWNB_FilterFold.run keep n q).source=q.source := by
 induction n generalizing q with
 | zero => rfl
 | succ n ih =>
  rw [PV_OWNB_FilterFold.run,ih]
  unfold PV_OWNB_FilterStep.step
  split <;> rfl

theorem generation (keep : Link → Bool) (n : Nat) (q : Cursor) :
 (PV_OWNB_FilterFold.run keep n q).token=q.token ∧
 (PV_OWNB_FilterFold.run keep n q).memory.generations=q.memory.generations := by
 induction n generalizing q with
 | zero => exact ⟨rfl,rfl⟩
 | succ n ih =>
  rw [PV_OWNB_FilterFold.run]
  obtain ⟨ht,hg⟩:=ih (PV_OWNB_FilterStep.step keep q)
  obtain ⟨st,sg⟩:=PV_OWNB_FilterStep.generation keep q
  exact ⟨ht.trans st,hg.trans sg⟩
#print axioms source
#print axioms generation
end R1Z.PV_OWNB_FilterIdentity
