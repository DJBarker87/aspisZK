import NLM_SevenSnapshots
import NLM_SnapshotReturned
set_option autoImplicit false
noncomputable section
namespace NLM_SevenReturned
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry
open NLM_Snapshot NLM_SevenSnapshots
/-- A returned seven-snapshot call identifies the stored values without
assuming allocation success. Each previous native cut supplies the next state. -/
theorem entered (e : Entry) (t : Nat) (owned : List NLM_Snapshot.Owned) (cs : List Site)
 (allocation : Site → Result Unit) (post : State)
 (success : (NLM_SevenSnapshots.G allocation cs (ready e t owned)).result=.ok post) :
 post=ready e (t+cs.length) (owned++ownedValues e cs) := by
 induction cs generalizing t owned post with
 | nil =>
   simp only [NLM_SevenSnapshots.G,NJU_Log.erase_pure] at success
   cases success
   simp [ownedValues]
 | cons c cs ih =>
   simp only [NLM_SevenSnapshots.G,NJU_Log.erase_bind] at success
   cases head : (NLM_Snapshot.G (ready e t owned) c.account c.lo c.hi (allocation c)).result with
   | fail err => rw [head] at success; cases success
   | div => rw [head] at success; cases success
   | ok pair =>
     rcases pair with ⟨value,mid⟩
     obtain ⟨_,same⟩ := returned_state e t c.account c.lo c.hi owned (allocation c) value mid head
     subst mid
     rw [head] at success
     change (NLM_SevenSnapshots.G allocation cs (ready e (t+1) (owned++[e.snapshot c.account c.lo c.hi]))).result=.ok post at success
     have h := ih (t+1) (owned++[e.snapshot c.account c.lo c.hi]) post success
     simpa [ownedValues,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
#print entered
#print axioms entered
end NLM_SevenReturned
