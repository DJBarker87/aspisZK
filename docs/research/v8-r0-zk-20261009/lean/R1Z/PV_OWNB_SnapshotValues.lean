import R1Z.PV_OWNB_SnapshotFold
import R1Z.PV_OWNB_ActualPrefix
import R1Z.PV_OWNB_ValueFold
set_option autoImplicit false
namespace R1Z.PV_OWNB_SnapshotValues
open PV_OWNB_Cursor PV_OWN_Link

theorem step (keep : Link → Bool) (q : Cursor) :
 PV_OWNB_Prefix.values (PV_OWNB_SnapshotStep.step keep q)=
 PV_OWNB_Prefix.values q++(if keep (q.source q.read) then [q.source q.read] else []) := by
 unfold PV_OWNB_SnapshotStep.step
 split
 · rw [PV_OWNB_ActualPrefix.sink,PV_OWNB_Prefix.advance]
 · rw [PV_OWNB_Prefix.advance,List.append_nil]

theorem source (keep : Link → Bool) (q : Cursor) :
 (PV_OWNB_SnapshotStep.step keep q).source=q.source := by
 unfold PV_OWNB_SnapshotStep.step
 split <;> rfl

theorem values (keep : Link → Bool) (n : Nat) (q : Cursor) :
 PV_OWNB_Prefix.values (PV_OWNB_SnapshotFold.run keep n q)=
 PV_OWNB_Prefix.values q++PV_OWNB_ValueFold.selected keep q.source q.read n := by
 induction n generalizing q with
 | zero => simp [PV_OWNB_SnapshotFold.run,PV_OWNB_ValueFold.selected]
 | succ n ih =>
  rw [PV_OWNB_SnapshotFold.run,ih,step,PV_OWNB_SnapshotStep.advances,source]
  simp only [PV_OWNB_ValueFold.selected,List.append_assoc]
#print axioms step
#print axioms source
#print axioms values
end R1Z.PV_OWNB_SnapshotValues
