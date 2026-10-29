import R1Z.PV_RunJoin_WeightInstalled46
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SamplerFields49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected

theorem ordinary (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base)) :
    @ExternalFuns.op250 (types base) (selected base heap box ops)=PV_B2_E_Install250.callback := rfl

theorem gamma (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base)) :
    @ExternalFuns.op249 (types base) (selected base heap box ops)=PV_B2_E_GammaOriginal.callback := rfl
#print axioms ordinary
#print axioms gamma
end R1Z.PV_RunJoin_SamplerFields49
