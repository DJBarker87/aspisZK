import R1Z.PV_RunJoin_ClaimProducerCell48
import R1Z.PV_DL_EncoderNative
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimEvaluator48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_RunJoin_ClaimThread48 (Column Point)

/-- One field projection, separate from any evaluation or byte bind. -/
theorem candidate [t : ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op79 t (ProverRwP6BodyCandidate.selected ops)=@ExternalFuns.op79 t ops := rfl

set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

/-- Explicit encoder-installed specialization; this does not assert which
upstream runtime dictionary the deployed caller supplies. -/
theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (point : Point) (column : Column) :
    PV_RunJoin_ClaimProducerCell48.evaluate base heap box
      (@PV_DL_EncoderSelected.selected (types base) ops) point column=
      PV_DL_EncoderNative.value
        (@aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField
          (types base) (selected base heap box (@PV_DL_EncoderSelected.selected (types base) ops)))
        column point := by
  unfold PV_RunJoin_ClaimProducerCell48.evaluate
  rw [candidate]
  exact @PV_DL_EncoderNative.selected_native (types base) ops _ _ column point
#print axioms candidate
#print axioms complete
end R1Z.PV_RunJoin_ClaimEvaluator48
