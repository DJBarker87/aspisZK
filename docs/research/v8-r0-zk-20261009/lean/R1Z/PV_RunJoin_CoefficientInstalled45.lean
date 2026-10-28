import R1Z.PV_RunJoin_CoefficientSampler45
import R1Z.PV_RunJoin_CoefficientBinding45
import R1Z.PV_RunJoin_CoefficientContext45
import R1Z.PV_RunJoin_CoefficientTagInstall45
import R1Z.PV_RunJoin_CoefficientTagSelected45
import R1Z.PV_RunJoin_CoefficientGuards45
import R1Z.PV_RunJoin_CoefficientHeap45
import R1Z.PV_RunJoin_CoefficientError45
import R1Z.PV_RunJoin_CoefficientNeg45
import R1Z.PV_RunJoin_CoefficientWide45
import R1Z.PV_RunJoin_CoefficientBody45
import R1Z.PV_RunJoin_CoefficientTransition45
import R1Z.PV_RunJoin_CoefficientFlat45
import R1Z.PV_RunJoin_CoefficientBoundary45
import R1Z.PV_RunJoin_CoefficientArray44
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CoefficientInstalled45
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
-- Reducibility hints only; kernel checking and resource limits are unchanged.
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwFullSampler.install ProverRwCallerBinding.install ProverRwOuterContext.install ProverRwOuterTag.install ProverRwOuterTag.selected ProverRwOuterGuardLeaves.selected ProverRwSuccessHeapInstall.selected ProverRwSuccessErrorInstall.selected ProverRwSuccessNativeNegInstall.selected ProverRwSuccessNativeWideInstall.selected ProverRwBodyNativeWideInstall.selected ProverRwP6TransitionInstall.selected ProverRwP6FlatInstall.selected ProverRwP6BoundaryInstall.selected ProverRwSuccessBodyInterpretation.selected

theorem guards (ops : ExternalFuns) {T : Type} :
    @ExternalFuns.op255 _ (ProverRwOuterGuardLeaves.selected ops) T = @ExternalFuns.op255 _ ops T := by
  rw [PV_RunJoin_CoefficientGuards45.preservation,
    PV_RunJoin_CoefficientTagSelected45.preservation,
    PV_RunJoin_CoefficientBinding45.preservation,
    PV_RunJoin_CoefficientSampler45.preservation,
    PV_RunJoin_CoefficientTagInstall45.preservation,
    PV_RunJoin_CoefficientContext45.preservation]

theorem source (ops : ExternalFuns) {T : Type} (copy : core.marker.Copy T) (rows : Array T 1024#usize) :
    @transport.Variant.coefficients _ (ProverRwP6BodyCandidate.selected ops) T copy .S2 rows =
      ProverRwSuccessCoefficientsSource.transport.Variant.coefficients copy .S2 rows := by
  change (ProverRwP6BoundaryInstall.selected ops).op255 copy .S2 rows = _
  rw [PV_RunJoin_CoefficientBoundary45.preservation,
    PV_RunJoin_CoefficientFlat45.preservation,
    PV_RunJoin_CoefficientTransition45.preservation,
    PV_RunJoin_CoefficientBody45.preservation, guards,
    PV_RunJoin_CoefficientWide45.preservation,
    PV_RunJoin_CoefficientNeg45.preservation,
    PV_RunJoin_CoefficientError45.preservation,
    PV_RunJoin_CoefficientHeap45.preservation]
  exact ProverRwSuccessBodyInterpretation.coefficients_s2 ops copy rows

theorem complete (ops : ExternalFuns) {T : Type} (copy : core.marker.Copy T) (xs : Nat → T) :
    @transport.Variant.coefficients _ (ProverRwP6BodyCandidate.selected ops) T copy .S2
      (ProverCommitArray49.array 1024#usize xs) =
      .ok (ProverCommitArray49.array 1024#usize (fun j => xs (AspisR1.rowNat j))) := by
  rw [source]
  exact PV_RunJoin_CoefficientArray44.complete copy ProverRwSuccessCoefficientsSource.transport.Variant.S2 xs
#print axioms guards
#print axioms source
#print axioms complete
end R1Z.PV_RunJoin_CoefficientInstalled45
