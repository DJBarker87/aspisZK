import PCD_LaneBridge
import PCD_Observe
set_option autoImplicit false
namespace PCD_Row320
open Aeneas Aeneas.Std PCD PCD_LaneRef
inductive TransitionKind where
  | privateTransfer | withdrawal
structure TerminalResult where
  transition_kind : TransitionKind
  master_account : Array U8 32#usize
  selected_lane_account : Array U8 32#usize
  output_lane : U8
  nullifier : Array U32 8#usize
  verified_afterstate : After

/-- Full own-argument carrier. The actual frozen body reads ONLY
verified_afterstate; native generators quantify independently over every
other field and both transition constructors. No canonicality/capacity or
successful endpoint is an argument-domain premise. -/
def nativeSegments (lane : Lane) (result : TerminalResult) : Result (Exit Lane) :=
  PCD_LaneBridge.run lane result.verified_afterstate
noncomputable def RowSpec_POOL_320 (lane : Lane) (result : TerminalResult) : Exit Lane :=
  PCD_LaneModel.specification lane result.verified_afterstate

theorem result_state_effects {State : Type} (lane : Lane) (result : TerminalResult) (state : State) :
    (nativeSegments lane result,state,([] : List PCD.Event)) =
      (.ok (RowSpec_POOL_320 lane result),state,[]) :=
  PCD_LaneBridge.result_state_effects lane result.verified_afterstate state

/-- EXACT own-input clauses needed if a future P3 producer wants this step
to succeed. This is not NIB-P3: the deployed image encoder/Box row319/315 and
their SAME-argument packets remain required. -/
theorem success_clause (lane : Lane) (result : TerminalResult)
    (increment : U64.checked_add lane.tree.next_leaf_index 1#u64 =
      some result.verified_afterstate.next_pair_index)
    (sparse : PCD_LaneLoop.good (PCD_LaneModel.tests result.verified_afterstate) 0 20) :
    nativeSegments lane result =
      .ok (.ok (PCD_LaneValue.candidate lane result.verified_afterstate)) := by
  rw [nativeSegments,PCD_LaneBridge.extracted_segments,PCD_LaneModel.result]
  unfold PCD_LaneModel.specification
  rw [if_pos increment,if_pos sparse]

#print axioms result_state_effects
#print axioms success_clause
end PCD_Row320
