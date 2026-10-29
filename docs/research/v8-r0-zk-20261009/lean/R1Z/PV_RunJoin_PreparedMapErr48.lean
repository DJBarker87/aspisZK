import R1Z.PV_RunJoin_PreparedDomain48
import R1Z.PV_RunJoin_WeightInstalled46
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PreparedMapErr48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46

theorem candidate [t : ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op12 t (ProverRwP6BodyCandidate.selected ops)=@ProverRwOuterMapErr.map_err := rfl

set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected

theorem field (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @ExternalFuns.op12 (types base) (selected base heap box ops)=@ProverRwOuterMapErr.map_err := by
  unfold selected
  rw [PV_B2_F_RawNative.preserved_12]
  exact @candidate (types base) ops

attribute [local irreducible] selected PV_B2_F_RawNative.selected

theorem success (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (folded : alloc.vec.Vec aspis_core.field.wide_exact.WideExact) :
    @core.result.Result.map_err (types base) (selected base heap box ops) _ _ _ _
      prover.prepare_opening.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError (.Ok folded) ()=ok (.Ok folded) := by
  change @ExternalFuns.op12 (types base) (selected base heap box ops) _ _ _ _ _ _ _=_
  rw [field]
  rfl

theorem error (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (e : aspis_core.r0.Error) :
    @core.result.Result.map_err (types base) (selected base heap box ops)
      (alloc.vec.Vec aspis_core.field.wide_exact.WideExact) _ _ _
      prover.prepare_opening.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError (.Err e) ()=ok (.Err verifier.Error.Allocation) := by
  change @ExternalFuns.op12 (types base) (selected base heap box ops) _ _ _ _ _ _ _=_
  rw [field]
  rfl
#print axioms candidate
#print axioms field
#print axioms success
#print axioms error
end R1Z.PV_RunJoin_PreparedMapErr48
