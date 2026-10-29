import R1Z.PV_OWNB_SnapshotStep
set_option autoImplicit false
namespace R1Z.PV_OWNB_SnapshotFold
open PV_OWNB_Cursor PV_OWN_Link

def run (keep : Link → Bool) : Nat → Cursor → Cursor
 | 0,q => q
 | n+1,q => run keep n (PV_OWNB_SnapshotStep.step keep q)

theorem valid (keep : Link → Bool) (n : Nat) (q : Cursor)
 (h:Valid q) (enough:q.read+n≤q.length) : Valid (run keep n q) := by
 induction n generalizing q with
 | zero => exact h
 | succ n ih =>
  apply ih
  · exact PV_OWNB_SnapshotStep.valid keep q h (by omega)
  · rw [PV_OWNB_SnapshotStep.advances,PV_OWNB_SnapshotStep.length]
    omega

theorem advances (keep : Link → Bool) (n : Nat) (q : Cursor) :
 (run keep n q).read=q.read+n := by
 induction n generalizing q with
 | zero => rfl
 | succ n ih =>
  rw [run,ih,PV_OWNB_SnapshotStep.advances]
  omega
attribute [local irreducible] run
#print axioms valid
#print axioms advances
end R1Z.PV_OWNB_SnapshotFold
