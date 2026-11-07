import PCD_SegmentCalls
import PCD_LaneRange
set_option autoImplicit false
namespace PCD_LaneBridge
open Aeneas Aeneas.Std PCD PCD_LaneRef PCD_LaneLoop

def run (lane : Lane) (after : After) : Result (Exit Lane) := do
  let incrementMatches ← checked_next lane.tree.next_leaf_index after.next_pair_index
  if incrementMatches then
    let scanned ← PCD_SegmentCalls.scanCalls after 0 20
    match scanned with
    | .rejected _ => .ok (.error (.custom 0x41532003))
    | .done _ => do
      let value ← finish_lane lane after
      .ok (.ok value)
  else .ok (.error (.custom 0x41532003))

/-- All three extracted primitives compose in source order, retaining the
first Err and complete returned value. Native certificates and reviewed source
association are external evidence, not hypotheses hidden inside this theorem. -/
theorem extracted_segments (lane : Lane) (after : After) :
    run lane after = .ok (PCD_LaneModel.source lane after) := by
  unfold run PCD_LaneModel.source PCD_LaneResult.source
  rw [PCD_Checked.reference_exact]
  simp only [bind_tc_ok]
  split
  · rw [PCD_SegmentCalls.scan_exact]
    simp only [bind_tc_ok]
    cases scan (PCD_LaneModel.tests after) 0 20 with
    | rejected rejectedLevel => rfl
    | done finalLevel => rw [PCD_LaneValue.finish_exact]; rfl
  · rfl

theorem result_state_effects {State : Type} (lane : Lane) (after : After) (state : State) :
    (run lane after,state,([] : List PCD.Event)) =
      (.ok (PCD_LaneModel.specification lane after),state,[]) := by
  rw [extracted_segments,PCD_LaneModel.result]
#print axioms extracted_segments
#print axioms result_state_effects
end PCD_LaneBridge
