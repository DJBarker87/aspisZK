import R1Z.PV_RunJoin_EncodedCongruence48
import R1Z.PV_RunJoin_ClaimFields48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_EncodedInstalled48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_RunJoin_EncodedCongruence48 (W)
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem field (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @ExternalFuns.op51 (types base) (selected base heap box ops)=
      (@ProverRwP6BodyCandidate.selected (types base) ops).op51 := by
  funext x
  exact (PV_RunJoin_ClaimFields48.serializer base heap box ops x).trans
    (@PV_RunJoin_FlatBytes35.installed (types base) ops x).symm

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (values : Slice W) :
    @prover.encoded_slice (types base) (selected base heap box ops) values=
      @prover.encoded_slice (types base) (@ProverRwP6BodyCandidate.selected (types base) ops) values :=
  @PV_RunJoin_EncodedCongruence48.complete (types base) _ _ (field base heap box ops) values
#print axioms field
#print axioms complete
end R1Z.PV_RunJoin_EncodedInstalled48
