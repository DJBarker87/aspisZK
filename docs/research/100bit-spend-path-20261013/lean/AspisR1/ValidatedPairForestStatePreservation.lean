import AspisR1.ValidatedAppendAfterstate
import R1AppendStateIndex

/-! The selected validator's successful terminal transition can be composed
with the Pool append-state invariant.  This is the mathematical preservation
fact needed by the source-invariant decoder/encoder: the old authenticated
frontier remains an explicit premise, while source account/PDA ownership and
the atomic Rust write remain separate refinement obligations. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.ValidatedPairForestStatePreservation

open Aeneas Aeneas.Std
open R0P AspisCircleGroupOrder AspisPool.IncrementalMerkleV1

abbrev K := AspisR1.ValidatedAppendAfterstate.K
abbrev Public := AspisR1.ValidateTransitionConcreteExact.Public
abbrev exactPublic := AspisR1.SemanticPublicModel.exactPublic
abbrev FrontierInvariant {α : Type} :=
  AspisPool.IncrementalMerkleV1.FrontierInvariant (α := α)
abbrev StateLink {K : Type} [Field K] (pub next : R0P.Public K) :=
  AspisR1.AppendStateIndex.StateLink pub next

local instance exactQMCharP : CharP K AspisCircleGroupOrder.P :=
  charP_of_injective_algebraMap
    (algebraMap AspisV8R15.ExactTowerBase.M31Exact K).injective
    AspisCircleGroupOrder.P

attribute [local irreducible] nodeCompress poseidonPermutation

/-- A successful concrete validation, production/copy relation, and the
previous authenticated Pool frontier invariant jointly establish the exact
post-append state facts.  `StateFacts` separates the ordinary open-capacity
case from the terminal full-capacity case. -/
theorem successful_terminal_preserves_state
    (public1 : Public) (trace : R0P.Trace K) (lambda chi : K)
    (hproduction : R0P.ProductionHolds (exactPublic public1) lambda chi trace ∧
      R0P.CopyLinkBalance (exactPublic public1) trace)
    (hsuccess : AspisR1.ValidateTransitionConcreteExact.source public1 =
      Aeneas.Std.Result.ok (core.result.Result.Ok ()))
    (leaves : List (R0P.Digest K))
    (oldInvariant : FrontierInvariant nodeCompress
      AspisR1.AppendTreeRoot.emptyPair 20 leaves
      (AspisR1.AppendTreeRoot.sourceFrontier (exactPublic public1))) :
    AspisR1.AppendTreeState.StateFacts (exactPublic public1)
      (AspisR1.OutputNotes.output trace 33) leaves := by
  have hshape := AspisR1.ValidateTransitionConcreteExact.successful_concrete_noncarry_shape
    public1 hsuccess
  exact AspisR1.AppendTreeState.of_production (exactPublic public1) trace lambda chi
    hproduction hshape leaves oldInvariant |>.2

/-- When the Pool's next invocation reads the exact saved cursor and frontier,
the open-capacity post-state above is a valid source frontier for that spend.
The source `StateLink` is deliberately a premise: account serializer equality,
PDA/owner checks, and atomic account mutation must establish it. -/
theorem successful_terminal_then_next_open_invariant
    (public1 nextPublic : Public) (trace : R0P.Trace K) (lambda chi : K)
    (hproduction : R0P.ProductionHolds (exactPublic public1) lambda chi trace ∧
      R0P.CopyLinkBalance (exactPublic public1) trace)
    (hsuccess : AspisR1.ValidateTransitionConcreteExact.source public1 =
      Aeneas.Std.Result.ok (core.result.Result.Ok ()))
    (leaves : List (R0P.Digest K))
    (oldInvariant : FrontierInvariant nodeCompress
      AspisR1.AppendTreeRoot.emptyPair 20 leaves
      (AspisR1.AppendTreeRoot.sourceFrontier (exactPublic public1)))
    (oldOpen : (exactPublic public1).nextPairIndex < 2 ^ 20)
    (link : StateLink (exactPublic public1) (exactPublic nextPublic))
    (nextOpen : (exactPublic nextPublic).nextPairIndex < 2 ^ 20) :
    FrontierInvariant nodeCompress
      AspisR1.AppendTreeRoot.emptyPair 20
      (leaves ++ [AspisR1.OutputNotes.output trace 33])
      (AspisR1.AppendTreeRoot.sourceFrontier (exactPublic nextPublic)) := by
  have hshape := AspisR1.ValidateTransitionConcreteExact.successful_concrete_noncarry_shape
    public1 hsuccess
  have hstate := AspisR1.AppendTreeState.of_production (exactPublic public1)
    trace lambda chi hproduction hshape leaves oldInvariant
  exact AspisR1.AppendStateIndex.next_invariant (exactPublic public1)
    (exactPublic nextPublic) (AspisR1.OutputNotes.output trace 33) leaves oldOpen
    oldInvariant hstate.2 link nextOpen

#print axioms successful_terminal_preserves_state
#print axioms successful_terminal_then_next_open_invariant

end AspisR1.ValidatedPairForestStatePreservation
end
