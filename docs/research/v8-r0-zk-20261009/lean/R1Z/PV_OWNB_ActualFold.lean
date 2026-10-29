import R1Z.PV_OWNB_ActualFilter
set_option autoImplicit false
namespace R1Z.PV_OWNB_ActualFold
open PV_OWNB_Cursor PV_OWN_Link PV_OWN_Bytes PV_OWNB_Padding

def run (keep : Link → Bool) (bytes : Nat → Link → Bytes) : Nat → Cursor → Cursor
 | 0,q => q
 | n+1,q => run keep bytes n (PV_OWNB_ActualFilter.step keep bytes q)

theorem advances (keep : Link → Bool) (bytes : Nat → Link → Bytes) (n : Nat) (q : Cursor) :
 (run keep bytes n q).read=q.read+n := by
 induction n generalizing q with
 | zero => rfl
 | succ n ih =>
  rw [run,ih,PV_OWNB_ActualFilter.advances]
  omega

theorem length (keep : Link → Bool) (bytes : Nat → Link → Bytes) (n : Nat) (q : Cursor) :
 (run keep bytes n q).length=q.length := by
 induction n generalizing q with
 | zero => rfl
 | succ n ih =>
  rw [run,ih]
  unfold PV_OWNB_ActualFilter.step
  split <;> rfl

theorem valid (keep : Link → Bool) (bytes : Nat → Link → Bytes) (n : Nat) (q : Cursor)
 (h:Valid q) (enough:q.read+n≤q.length)
 (copy:∀ i v, Agrees (PV_OWNB_LinkBytes.encode v) (bytes i v)) :
 Valid (run keep bytes n q) := by
 induction n generalizing q with
 | zero => exact h
 | succ n ih =>
  apply ih
  · apply PV_OWNB_ActualFilter.valid keep bytes q h (by omega) (copy _ _)
  · rw [PV_OWNB_ActualFilter.advances]
    have len:(PV_OWNB_ActualFilter.step keep bytes q).length=q.length := by
     unfold PV_OWNB_ActualFilter.step
     split <;> rfl
    rw [len]; omega
attribute [local irreducible] run
#print axioms advances
#print axioms length
#print axioms valid
end R1Z.PV_OWNB_ActualFold
