import AspisR1.ValidateTransitionConcreteExact

/-! Reuse the retained append-gate theorem with the source-derived guard fact. -/
set_option autoImplicit false
namespace AspisR1.ValidatedAppendAfterstate
noncomputable section
open Aeneas Aeneas.Std Result
abbrev K := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Public := AspisR1.ValidateTransitionConcreteExact.Public
abbrev exactPublic := AspisR1.SemanticPublicModel.exactPublic

theorem afterstate_of_successful_validation (prime : Nat) [CharP K prime]
    (hprime : prime = 2^31-1) (public1 : Public) (trace : R0P.Trace K) (lambda chi : K)
    (hproduction : R0P.ProductionHolds (exactPublic public1) lambda chi trace ∧
      R0P.CopyLinkBalance (exactPublic public1) trace)
    (hsuccess : AspisR1.ValidateTransitionConcreteExact.source public1 = .ok (.Ok ())) :
    AspisR1.AppendSemantics.GateFacts (exactPublic public1) trace ∧
      (exactPublic public1).nextFrontier = AspisR1.AppendSemantics.expectedFrontier
        (exactPublic public1) (AspisR1.OutputNotes.output trace 33) := by
  exact AspisR1.AppendSemantics.afterstate_of_production prime hprime
    (exactPublic public1) trace lambda chi hproduction
    (AspisR1.ValidateTransitionConcreteExact.successful_concrete_noncarry_shape public1 hsuccess)

#print axioms afterstate_of_successful_validation
end
end AspisR1.ValidatedAppendAfterstate
