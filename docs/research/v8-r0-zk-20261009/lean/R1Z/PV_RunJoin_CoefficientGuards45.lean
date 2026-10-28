import R1Z.ProverRwP6BodyCandidate
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CoefficientGuards45
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
attribute [local -reducible] ProverRwFullSampler.install ProverRwCallerBinding.install ProverRwOuterContext.install ProverRwOuterTag.install ProverRwOuterTag.selected ProverRwOuterGuardLeaves.selected ProverRwSuccessHeapInstall.selected ProverRwSuccessErrorInstall.selected ProverRwSuccessNativeNegInstall.selected ProverRwSuccessNativeWideInstall.selected ProverRwBodyNativeWideInstall.selected ProverRwP6TransitionInstall.selected ProverRwP6FlatInstall.selected ProverRwP6BoundaryInstall.selected ProverRwSuccessBodyInterpretation.selected
attribute [local irreducible] ProverRwFullSampler.install ProverRwCallerBinding.install ProverRwOuterContext.install ProverRwOuterTag.install ProverRwOuterTag.selected ProverRwOuterGuardLeaves.selected ProverRwSuccessHeapInstall.selected ProverRwSuccessErrorInstall.selected ProverRwSuccessNativeNegInstall.selected ProverRwSuccessNativeWideInstall.selected ProverRwBodyNativeWideInstall.selected ProverRwP6TransitionInstall.selected ProverRwP6FlatInstall.selected ProverRwP6BoundaryInstall.selected ProverRwSuccessBodyInterpretation.selected
-- Only the op255 projection is reduced, with predecessor dictionaries opaque.
theorem preservation (ops : ExternalFuns) {T : Type} :
    @ExternalFuns.op255 _ (ProverRwOuterGuardLeaves.selected ops) T =
      @ExternalFuns.op255 _ (ProverRwOuterTag.selected {ops with op112 := ProverRwOuterGuardLeaves.mask, op113 := ProverRwOuterGuardLeaves.factor}) T := by
  unfold ProverRwOuterGuardLeaves.selected
  rfl
#print axioms preservation
end R1Z.PV_RunJoin_CoefficientGuards45
