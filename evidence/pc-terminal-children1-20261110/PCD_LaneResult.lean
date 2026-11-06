import PCD_LaneLoop
import PCD_LaneValue
set_option autoImplicit false
namespace PCD_LaneResult
open PCD PCD_LaneRef PCD_LaneLoop
/-- Pure mathematical interpretation. Not a native RowSpec or adopted cohort replacement.
`test` is the per-level condition whose emitted/native association is still required. -/
def source (lane : Lane) (after : After) (incrementMatches : Bool)
    (test : Nat → Bool) : Exit Lane :=
  if incrementMatches then
    match scan test 0 20 with
    | .rejected _ => .error (.custom 0x41532003)
    | .done _ => .ok (PCD_LaneValue.candidate lane after)
  else .error (.custom 0x41532003)

theorem checked_rejection (lane : Lane) (after : After) (test : Nat → Bool) :
    source lane after false test = .error (.custom 0x41532003) := rfl

theorem frontier_rejection (lane : Lane) (after : After) (test : Nat → Bool)
    (offset tail : Nat) (extent : offset+tail+1 = 20)
    (earlier : good test 0 offset) (bad : test offset = false) :
    source lane after true test = .error (.custom 0x41532003) := by
  have h := first_failure test 0 offset tail earlier (by simpa using bad)
  simp only [Nat.zero_add] at h
  simp only [source, ↓reduceIte, ← extent, h]

theorem successful_value (lane : Lane) (after : After) (test : Nat → Bool)
    (all : good test 0 20) :
    source lane after true test = .ok (PCD_LaneValue.candidate lane after) := by
  have h := (scan_done_iff test 0 20).2 all
  simp only [source, ↓reduceIte, h]

#print axioms checked_rejection
#print axioms frontier_rejection
#print axioms successful_value
end PCD_LaneResult
