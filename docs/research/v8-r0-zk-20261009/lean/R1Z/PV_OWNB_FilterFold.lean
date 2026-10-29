import R1Z.PV_OWNB_FilterStep
set_option autoImplicit false
namespace R1Z.PV_OWNB_FilterFold
open PV_OWNB_Cursor PV_OWN_Link
/-- Bounded source walk, not kernel reduction of a concrete 127-link schedule. -/
def run (keep : Link → Bool) : Nat → Cursor → Cursor
 | 0,q => q
 | n+1,q => run keep n (PV_OWNB_FilterStep.step keep q)

theorem advances (keep : Link → Bool) (n : Nat) (q : Cursor) :
 (run keep n q).read=q.read+n := by
 induction n generalizing q with
 | zero => rfl
 | succ n ih =>
  rw [run,ih,PV_OWNB_FilterStep.advances]
  omega

theorem length (keep : Link → Bool) (n : Nat) (q : Cursor) :
 (run keep n q).length=q.length := by
 induction n generalizing q with
 | zero => rfl
 | succ n ih =>
  rw [run,ih]
  unfold PV_OWNB_FilterStep.step
  split <;> rfl

theorem valid (keep : Link → Bool) (n : Nat) (q : Cursor)
 (h:Valid q) (enough:q.read+n≤q.length) : Valid (run keep n q) := by
 induction n generalizing q with
 | zero => exact h
 | succ n ih =>
  apply ih
  · apply PV_OWNB_FilterStep.valid keep q h; omega
  · rw [PV_OWNB_FilterStep.advances]
    have len:(PV_OWNB_FilterStep.step keep q).length=q.length := by
     unfold PV_OWNB_FilterStep.step
     split <;> rfl
    rw [len]; omega
attribute [local irreducible] run
#print axioms advances
#print axioms length
#print axioms valid
end R1Z.PV_OWNB_FilterFold
