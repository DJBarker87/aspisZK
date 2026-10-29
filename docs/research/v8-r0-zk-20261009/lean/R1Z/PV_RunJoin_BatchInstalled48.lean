import R1Z.PV_RunJoin_BatchFields48
import R1Z.PV_RunJoin_BatchCongruence48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BatchInstalled48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_RunJoin_BatchRowThread44 (W Coefficients)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (coefficients : Coefficients) (g : W) :
    @prover.opening_batch (types base) (selected base heap box ops) coefficients g=
      @prover.opening_batch (types base) (@ProverRwP6BodyCandidate.selected (types base) ops) coefficients g := by
  apply @PV_RunJoin_BatchCongruence48.complete (types base)
    (selected base heap box ops) (@ProverRwP6BodyCandidate.selected (types base) ops)
    (PV_RunJoin_BatchFields48.zero base heap box ops)
    (PV_RunJoin_BatchFields48.mul base heap box ops)
    (PV_RunJoin_BatchFields48.add base heap box ops)
    (PV_RunJoin_BatchFields48.powers base heap box ops)
#print axioms complete
end R1Z.PV_RunJoin_BatchInstalled48
