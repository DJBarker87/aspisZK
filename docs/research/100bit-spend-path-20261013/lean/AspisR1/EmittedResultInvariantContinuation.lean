import AspisR1.EmittedResultStateLink
import AspisR1.ValidatedPairForestStatePreservation

/-! Reuse the proved append invariant with the source-derived state link.
The cryptographic production/Copy premise and persistent account readback
boundary remain explicit; neither is replaced by a runtime test. -/
set_option autoImplicit false
namespace AspisR1.EmittedResultInvariantContinuation
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1.EmittedResultStateLink
open AspisR1TerminalResultConstructorCut
abbrev K := AspisR1.ValidatedAppendAfterstate.K
abbrev exactPublic := AspisR1.SemanticPublicModel.exactPublic

local instance exactQMCharP : CharP K AspisCircleGroupOrder.P :=
  charP_of_injective_algebraMap
    (algebraMap AspisV8R15.ExactTowerBase.M31Exact K).injective
    AspisCircleGroupOrder.P

/-- The current successful validator, the production/Copy append relation and
actual emitted-value/lane-constructor successes preserve the next open spend's
frontier invariant, assuming only the stated raw account input/readback links
at the remaining persistence boundary. -/
theorem next_open_frontier_invariant
    (s : PoolV1PairForestTerminalStatementV1)
    (emitted : PoolV1PairForestTerminalResultV1)
    (old saved : Lane) (nextPublic : Public)
    (emptyRoots : Array (Array U32 8#usize) 21#usize)
    (hemit : emitted_result_value s = .ok emitted)
    (hwrite : AspisR1PairForestLaneWriteSourceCut.next_pair_forest_lane_v1
      old emptyRoots (AspisR1.EmittedResultLaneWrite.toLaneResult emitted) = .ok (.Ok saved))
    (hold : (semanticPublic s).transition.live_snapshot.next_pair_index = old.tree.next_leaf_index)
    (hreadIndex : nextPublic.transition.live_snapshot.next_pair_index = saved.tree.next_leaf_index)
    (hreadFrontier : nextPublic.transition.live_snapshot.frontier = saved.tree.frontier)
    (trace : R0P.Trace K) (lambda chi : K)
    (hproduction : R0P.ProductionHolds (exactPublic (semanticPublic s)) lambda chi trace ∧
      R0P.CopyLinkBalance (exactPublic (semanticPublic s)) trace)
    (hvalidation : AspisR1.ValidateTransitionConcreteExact.source (semanticPublic s) = .ok (.Ok ()))
    (leaves : List (R0P.Digest K))
    (oldInvariant : AspisPool.IncrementalMerkleV1.FrontierInvariant
      R0P.nodeCompress AspisR1.AppendTreeRoot.emptyPair 20 leaves
      (AspisR1.AppendTreeRoot.sourceFrontier (exactPublic (semanticPublic s))))
    (oldOpen : (exactPublic (semanticPublic s)).nextPairIndex < 2 ^ 20)
    (nextOpen : (exactPublic nextPublic).nextPairIndex < 2 ^ 20) :
    AspisPool.IncrementalMerkleV1.FrontierInvariant
      R0P.nodeCompress AspisR1.AppendTreeRoot.emptyPair 20
      (leaves ++ [AspisR1.OutputNotes.output trace 33])
      (AspisR1.AppendTreeRoot.sourceFrontier (exactPublic nextPublic)) := by
  exact AspisR1.ValidatedPairForestStatePreservation.successful_terminal_then_next_open_invariant
    (semanticPublic s) nextPublic trace lambda chi hproduction hvalidation leaves oldInvariant
    oldOpen (state_link_of_source_and_readback s emitted old saved nextPublic emptyRoots
      hemit hwrite hold hreadIndex hreadFrontier) nextOpen

#print axioms next_open_frontier_invariant
end
end AspisR1.EmittedResultInvariantContinuation
