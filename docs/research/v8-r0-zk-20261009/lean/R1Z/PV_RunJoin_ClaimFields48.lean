import R1Z.PV_RunJoin_WeightInstalled46
import R1Z.PV_RunJoin_FlatBytes35
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimFields48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected

theorem evaluator (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @ExternalFuns.op79 (types base) (selected base heap box ops)=
      @ExternalFuns.op79 (types base) (ProverRwP6BodyCandidate.selected ops) := by
  unfold selected
  exact PV_B2_F_RawNative.preserved_79 base heap box _

theorem serializer (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (x : aspis_core.field.wide_exact.WideExact) :
    @ExternalFuns.op51 (types base) (selected base heap box ops) x=
      ok (PV_RunJoin_FlatBytes35.wire x) := by
  unfold selected
  rw [PV_B2_F_RawNative.preserved_51]
  exact PV_RunJoin_FlatBytes35.installed ops x
#print axioms evaluator
#print axioms serializer
end R1Z.PV_RunJoin_ClaimFields48
