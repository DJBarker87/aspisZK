import R1Z.ProverRwP6BodyCandidate
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CoefficientBody45
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
-- Reducibility hints only; kernel checking and resource limits are unchanged.
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwFullSampler.install ProverRwCallerBinding.install ProverRwOuterContext.install ProverRwOuterTag.install ProverRwOuterTag.selected ProverRwOuterGuardLeaves.selected ProverRwSuccessHeapInstall.selected ProverRwSuccessErrorInstall.selected ProverRwSuccessNativeNegInstall.selected ProverRwSuccessNativeWideInstall.selected ProverRwBodyNativeWideInstall.selected ProverRwP6TransitionInstall.selected ProverRwP6FlatInstall.selected ProverRwP6BoundaryInstall.selected ProverRwSuccessBodyInterpretation.selected
-- Only the op255 projection is reduced, with predecessor dictionaries opaque.
theorem preservation (ops : ExternalFuns) {T : Type} :
    @ExternalFuns.op255 _ (ProverRwBodyNativeWideInstall.selected ops) T =
      @ExternalFuns.op255 _ (ProverRwOuterGuardLeaves.selected (ProverRwSuccessNativeWideInstall.selected ops)) T := by
  unfold ProverRwBodyNativeWideInstall.selected
  rfl
#print axioms preservation
end R1Z.PV_RunJoin_CoefficientBody45
