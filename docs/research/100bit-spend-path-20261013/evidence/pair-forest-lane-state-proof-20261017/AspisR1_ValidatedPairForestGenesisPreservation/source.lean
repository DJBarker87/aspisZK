import AspisR1.ValidatedPairForestStatePreservation

/-! A genesis cursor supplies the old frontier invariant for the first
authenticated terminal append. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.ValidatedPairForestGenesisPreservation

open Aeneas Aeneas.Std

abbrev K := AspisR1.ValidatedAppendAfterstate.K
abbrev Public := AspisR1.ValidateTransitionConcreteExact.Public
abbrev exactPublic := AspisR1.SemanticPublicModel.exactPublic

local instance exactQMCharP : CharP K AspisCircleGroupOrder.P :=
  charP_of_injective_algebraMap
    (algebraMap AspisV8R15.ExactTowerBase.M31Exact K).injective
    AspisCircleGroupOrder.P

theorem successful_genesis_terminal_preserves_state
    (public1 : Public) (trace : R0P.Trace K) (lambda chi : K)
    (hproduction : R0P.ProductionHolds (exactPublic public1) lambda chi trace ∧
      R0P.CopyLinkBalance (exactPublic public1) trace)
    (hsuccess : AspisR1.ValidateTransitionConcreteExact.source public1 =
      Aeneas.Std.Result.ok (core.result.Result.Ok ()))
    (hgenesis : (exactPublic public1).nextPairIndex = 0) :
    AspisR1.AppendTreeState.StateFacts (exactPublic public1)
      (AspisR1.OutputNotes.output trace 33) [] := by
  have hinv := AspisR1.AppendStateIndex.initial_invariant
    (exactPublic public1) hgenesis
  exact AspisR1.ValidatedPairForestStatePreservation.successful_terminal_preserves_state
    public1 trace lambda chi hproduction hsuccess [] hinv

#print axioms successful_genesis_terminal_preserves_state

end AspisR1.ValidatedPairForestGenesisPreservation
end
