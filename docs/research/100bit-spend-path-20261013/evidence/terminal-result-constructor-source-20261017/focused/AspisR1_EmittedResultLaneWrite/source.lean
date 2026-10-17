import AspisR1.TerminalResultConstructorFields
import AspisR1PairForestLaneWriteSourceCut.LaneWriteCheckedAddNat

/-! Fixed record map from the exact emitted constructor to the extracted Pool
lane constructor. The runtime byte transport of this record remains separate;
there is no independent afterstate-equality assumption in this composition. -/
set_option autoImplicit false
namespace AspisR1.EmittedResultLaneWrite
open Aeneas Aeneas.Std Result

def toLaneKind : AspisR1TerminalResultConstructorCut.PoolV1TransitionKind → AspisR1PairForestLaneWriteSourceCut.PoolV1TransitionKind
  | .PrivateTransfer => .PrivateTransfer
  | .Withdrawal => .Withdrawal

def toLaneResult (r : AspisR1TerminalResultConstructorCut.PoolV1PairForestTerminalResultV1) : AspisR1PairForestLaneWriteSourceCut.PoolV1PairForestTerminalResultV1 where
  transition_kind := toLaneKind r.transition_kind
  master_account := r.master_account
  selected_lane_account := r.selected_lane_account
  output_lane := r.output_lane
  nullifier := r.nullifier
  verified_afterstate :=
    { next_pair_index := r.verified_afterstate.next_pair_index
      next_root := r.verified_afterstate.next_root
      next_frontier := r.verified_afterstate.next_frontier }

/-- Successful execution of the actual emitted value followed by the actual
Pool helper writes the same statement's candidate afterstate and derives the
exact cursor increment. These two source functions do not independently
establish authenticated byte transport, persistent account writes, or the
statement's proof validity. -/
theorem successful_emission_then_lane
    (statement : AspisR1.TerminalResultConstructorFields.Statement) (emitted : AspisR1.TerminalResultConstructorFields.Output)
    (old next : AspisR1PairForestLaneWriteSourceCut.PoolV1PairForestLaneStateV1)
    (emptyRoots : Array (Array U32 8#usize) 21#usize)
    (hemit : AspisR1TerminalResultConstructorCut.emitted_result_value statement = .ok emitted)
    (hwrite : AspisR1PairForestLaneWriteSourceCut.next_pair_forest_lane_v1 old emptyRoots (toLaneResult emitted) =
      .ok (.Ok next)) :
    next.bump = old.bump ∧ next.master = old.master ∧ next.lane_id = old.lane_id ∧
    next.tree.next_leaf_index = (AspisR1.TerminalResultConstructorFields.common statement).lane_transition.candidate_afterstate.next_pair_index ∧
    next.tree.root = (AspisR1.TerminalResultConstructorFields.common statement).lane_transition.candidate_afterstate.next_root ∧
    next.tree.frontier = (AspisR1.TerminalResultConstructorFields.common statement).lane_transition.candidate_afterstate.next_frontier ∧
    next.tree.next_leaf_index.val = old.tree.next_leaf_index.val + 1 := by
  have hfields := AspisR1PairForestLaneWriteSourceCut.OutputProjection.next_pair_forest_lane_success_fields
    old emptyRoots (toLaneResult emitted) next hwrite
  have hindex := AspisR1PairForestLaneWriteSourceCut.OutputProjection.next_pair_forest_lane_success_checked_add_val
    old emptyRoots (toLaneResult emitted) next hwrite
  have hemitted := (AspisR1.TerminalResultConstructorFields.successful_source_fields statement emitted hemit).2.2.2.2.2
  rcases hfields with ⟨hb, hm, hl, hi, hr, hf⟩
  refine ⟨hb, hm, hl, ?_, ?_, ?_, ?_⟩
  · simpa only [toLaneResult, hemitted] using hi
  · simpa only [toLaneResult, hemitted] using hr
  · simpa only [toLaneResult, hemitted] using hf
  · exact (congrArg (fun x : U64 => x.val) hi).trans hindex

#print axioms successful_emission_then_lane
end AspisR1.EmittedResultLaneWrite
