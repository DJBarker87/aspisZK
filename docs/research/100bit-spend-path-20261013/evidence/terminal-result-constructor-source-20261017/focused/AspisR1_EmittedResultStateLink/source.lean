import AspisR1.EmittedResultLaneWrite
import SemanticPublicModel
import R1AppendStateIndex

/-! Connects actual source value construction and lane copying to the retained
state-index link. The remaining readback premises identify only the exact raw
cursor and frontier read on the next invocation; authenticated byte transport,
account mutation and those reads are not asserted by this module. -/
set_option autoImplicit false
namespace AspisR1.EmittedResultStateLink
open Aeneas Aeneas.Std Result
open AspisR1TerminalResultConstructorCut
open AspisR1SelectedMaskProbe
abbrev Public := AspisR1.SemanticPublicModel.Public
abbrev exactPublic := AspisR1.SemanticPublicModel.exactPublic
abbrev Lane := AspisR1PairForestLaneWriteSourceCut.PoolV1PairForestLaneStateV1

def toTransition (t : PoolV1PairLatePublicStatementV1) :
    pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 where
  live_snapshot :=
    { pool := t.live_snapshot.pool
      deployment_domain := t.live_snapshot.deployment_domain
      sequence := t.live_snapshot.sequence
      next_pair_index := t.live_snapshot.next_pair_index
      current_root := t.live_snapshot.current_root
      frontier := t.live_snapshot.frontier }
  candidate_afterstate :=
    { next_pair_index := t.candidate_afterstate.next_pair_index
      next_root := t.candidate_afterstate.next_root
      next_frontier := t.candidate_afterstate.next_frontier }

/-- Fixed full field map to the retained semantic carrier. This preserves the
same public projection as private_public/withdrawal_public; binding the actual
accepted caller to this statement remains separate. -/
def semanticPublic : PoolV1PairForestTerminalStatementV1 → Public
  | .PrivateTransfer c p =>
      { variant := .PrivateTransfer
        pool := p.pool
        deployment_domain := p.deployment_domain
        anchor := p.anchor_root
        nullifier := p.nullifier
        asset_id := p.asset_id
        recipient := some p.recipient_commitment
        change := p.change_commitment
        withdrawal_amount := none
        transition := toTransition c.lane_transition }
  | .Withdrawal c p =>
      { variant := .Withdrawal
        pool := p.pool
        deployment_domain := p.deployment_domain
        anchor := p.anchor_root
        nullifier := p.nullifier
        asset_id := p.asset_id
        recipient := none
        change := p.change_commitment
        withdrawal_amount := some p.amount
        transition := toTransition c.lane_transition }

theorem semantic_candidate_frontier (s : PoolV1PairForestTerminalStatementV1) :
    (semanticPublic s).transition.candidate_afterstate.next_frontier =
      (AspisR1.TerminalResultConstructorFields.common s).lane_transition.candidate_afterstate.next_frontier := by
  cases s <;> rfl

/-- No separate abstract `StateLink` or candidate-afterstate equality is assumed.
Actual source success derives the saved cursor/frontier; raw input/readback
identification remains explicit at the unproved account boundary. -/
theorem state_link_of_source_and_readback
    (s : PoolV1PairForestTerminalStatementV1)
    (emitted : PoolV1PairForestTerminalResultV1)
    (old saved : Lane) (nextPublic : Public)
    (emptyRoots : Array (Array U32 8#usize) 21#usize)
    (hemit : emitted_result_value s = .ok emitted)
    (hwrite : AspisR1PairForestLaneWriteSourceCut.next_pair_forest_lane_v1
      old emptyRoots (AspisR1.EmittedResultLaneWrite.toLaneResult emitted) = .ok (.Ok saved))
    (hold : (semanticPublic s).transition.live_snapshot.next_pair_index = old.tree.next_leaf_index)
    (hreadIndex : nextPublic.transition.live_snapshot.next_pair_index = saved.tree.next_leaf_index)
    (hreadFrontier : nextPublic.transition.live_snapshot.frontier = saved.tree.frontier) :
    AspisR1.AppendStateIndex.StateLink (exactPublic (semanticPublic s)) (exactPublic nextPublic) := by
  have hfields := AspisR1.EmittedResultLaneWrite.successful_emission_then_lane
    s emitted old saved emptyRoots hemit hwrite
  rcases hfields with ⟨_, _, _, _, _, hf, hi⟩
  constructor
  · change nextPublic.transition.live_snapshot.next_pair_index.val =
      (semanticPublic s).transition.live_snapshot.next_pair_index.val + 1
    rw [hreadIndex, hold]
    exact hi
  · have hfrontier : nextPublic.transition.live_snapshot.frontier =
        (semanticPublic s).transition.candidate_afterstate.next_frontier :=
      hreadFrontier.trans (hf.trans (semantic_candidate_frontier s).symm)
    change (fun i : Fin 20 => AspisR1.SemanticPublicModel.digest
      (nextPublic.transition.live_snapshot.frontier.val[i.val]'(by
        simpa [nextPublic.transition.live_snapshot.frontier.property] using i.isLt))) =
      (fun i : Fin 20 => AspisR1.SemanticPublicModel.digest
      ((semanticPublic s).transition.candidate_afterstate.next_frontier.val[i.val]'(by
        simpa [(semanticPublic s).transition.candidate_afterstate.next_frontier.property] using i.isLt)))
    simp only [hfrontier]

#print axioms semantic_candidate_frontier
#print axioms state_link_of_source_and_readback
end AspisR1.EmittedResultStateLink
