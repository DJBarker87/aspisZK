import R1Z.PV_RunJoin_WeightInstalled46
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_WeightAbsorb66
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
theorem coefficients (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @ProverRwSuccessBodyInterpretation.coefficients (types base) (selected base heap box ops)=
      @ProverRwSuccessBodyInterpretation.coefficients (types base) ops := by
  funext T copy variant rows
  cases variant <;> rfl
theorem frame (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @ProverRwP6BodyCandidate.selected (types base) (selected base heap box ops)=
      (letI : ExternalTypes := types base
       {selected base heap box ops with op255 :=
        @ProverRwSuccessBodyInterpretation.coefficients (types base) (selected base heap box ops)}) := by
  rfl
theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @ProverRwP6BodyCandidate.selected (types base) (selected base heap box ops)=
      selected base heap box ops := by
  rw [frame,coefficients]
  rfl
#print axioms coefficients
#print axioms frame
#print axioms complete
end R1Z.PV_RunJoin_WeightAbsorb66
