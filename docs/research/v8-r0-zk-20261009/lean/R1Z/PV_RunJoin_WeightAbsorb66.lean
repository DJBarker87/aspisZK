import R1Z.PV_RunJoin_WeightInstalled46
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_WeightAbsorb66
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
/-- Reinstalling the fixed prover leaves preserves the installed weight dictionary. -/
theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @ProverRwP6BodyCandidate.selected (types base) (selected base heap box ops)=
      selected base heap box ops := by
  apply ExternalFuns.ext <;> rfl
#print axioms complete
end R1Z.PV_RunJoin_WeightAbsorb66
