import R1Z.ProverRwP6BodyCandidate
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CoefficientTagInstall45
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
attribute [local irreducible] ProverRwFullSampler.install ProverRwCallerBinding.install ProverRwOuterContext.install ProverRwOuterTag.install ProverRwOuterTag.selected ProverRwOuterGuardLeaves.selected ProverRwSuccessHeapInstall.selected ProverRwSuccessErrorInstall.selected ProverRwSuccessNativeNegInstall.selected ProverRwSuccessNativeWideInstall.selected ProverRwBodyNativeWideInstall.selected ProverRwP6TransitionInstall.selected ProverRwP6FlatInstall.selected ProverRwP6BoundaryInstall.selected ProverRwSuccessBodyInterpretation.selected
-- Only the op255 projection is reduced, with predecessor dictionaries opaque.
theorem preservation (ops : ExternalFuns) {T : Type} :
    @ExternalFuns.op255 _ (ProverRwOuterTag.install ops) T =
      @ExternalFuns.op255 _ (ProverRwOuterContext.install ops) T := by
  unfold ProverRwOuterTag.install
  rfl
#print axioms preservation
end R1Z.PV_RunJoin_CoefficientTagInstall45
