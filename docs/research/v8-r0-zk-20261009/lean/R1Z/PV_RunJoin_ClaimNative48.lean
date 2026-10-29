import R1Z.PV_RunJoin_ClaimEvaluator48
import R1Z.PV_RunJoin_ClaimInstalled48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimNative48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_RunJoin_ClaimThread48 (Column Point W)
open PV_RunJoin_WeightMap46 (mapResult)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (columns : Slice Column) (point : Point)
    (small : columns.length≤14336) :
    let encoderOps := @PV_DL_EncoderSelected.selected (types base) ops
    let dictionary := selected base heap box encoderOps
    mapResult (fun out => out.val)
      (@prover.opening_claim_bytes (types base) dictionary columns point)=
      mapResult PV_RunJoin_ClaimImage48.bytes
        (PV_RunJoin_ClaimImage48.values (fun column => PV_DL_EncoderNative.value
          (@aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField
            (types base) dictionary) column point) columns.val) := by
  dsimp only
  rw [PV_RunJoin_ClaimInstalled48.complete base heap box _ columns point small]
  have he : PV_RunJoin_ClaimProducerCell48.evaluate base heap box
      (@PV_DL_EncoderSelected.selected (types base) ops) point=
      (fun column => PV_DL_EncoderNative.value
        (@aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField
          (types base) (selected base heap box (@PV_DL_EncoderSelected.selected (types base) ops))) column point) := by
    funext column
    exact PV_RunJoin_ClaimEvaluator48.complete base heap box ops point column
  rw [he]
#print axioms complete
end R1Z.PV_RunJoin_ClaimNative48
