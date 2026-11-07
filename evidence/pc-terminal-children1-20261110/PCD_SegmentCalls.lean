import PCD_LaneModel
set_option autoImplicit false
namespace PCD_SegmentCalls
open Aeneas Aeneas.Std PCD_LaneRef PCD_LaneLoop

def stepCall (after : After) (level : Nat) : Result Bool :=
  if h : level < 20 then
    frontier_step after.next_pair_index (PCD_LaneModel.levelWord level)
      (after.next_frontier.val[level]'(by rw [after.next_frontier.property]; exact h))
      (PCD_EmptyRoots.roots.val[level]'(by rw [PCD_EmptyRoots.roots.property]; exact h))
  else .ok false

theorem step_exact (after : After) (level : Nat) :
    stepCall after level = .ok (PCD_LaneModel.tests after level) := by
  unfold stepCall PCD_LaneModel.tests
  split
  · exact PCD_FrontierValue.reference_exact _ _ _ _
  · rfl

def scanCalls (after : After) (level : Nat) : Nat → Result Scan
  | 0 => .ok (.done level)
  | n+1 => do
    let accepted ← stepCall after level
    if accepted then scanCalls after (level+1) n else .ok (.rejected level)

/-- Generic induction over the extracted ONE-step reference; no concrete
recurrence, freely chosen Ops or successful-endpoint premise. -/
theorem scan_exact (after : After) (level n : Nat) :
    scanCalls after level n = .ok (scan (PCD_LaneModel.tests after) level n) := by
  induction n generalizing level with
  | zero => rfl
  | succ n ih =>
    rw [scanCalls, step_exact]
    simp only [bind_tc_ok]
    unfold scan
    split
    · exact ih (level+1)
    · rfl
#print axioms step_exact
#print axioms scan_exact
end PCD_SegmentCalls
