import R1Z.PV_RJN_NodeReject
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJN_NodeInstalled
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem primitive_bits [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op235 _ (ProverRwP6BodyCandidate.selected ops)=ok 18#u32 := by
  unfold ProverRwP6BodyCandidate.selected ProverRwP6BoundaryInstall.selected
  rfl

theorem primitive_batch [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op236 _ (ProverRwP6BodyCandidate.selected ops)=ok 16#usize := by
  unfold ProverRwP6BodyCandidate.selected ProverRwP6BoundaryInstall.selected
  rfl

theorem primitive_branch [ExternalTypes] (ops : ExternalFuns) (T : Type) :
    @ExternalFuns.op9 _ (ProverRwP6BodyCandidate.selected ops) T none=
      ok (core.ops.control_flow.ControlFlow.Break none) := by
  unfold ProverRwP6BodyCandidate.selected ProverRwP6BoundaryInstall.selected
  rfl

theorem primitive_residual [ExternalTypes] (ops : ExternalFuns) (T : Type) :
    @ExternalFuns.op10 _ (ProverRwP6BodyCandidate.selected ops) T none=ok none := by
  have entry : @ExternalFuns.op10 _ (ProverRwP6BodyCandidate.selected ops)=ProverRwDictionaryOption.Src.residual := by
    unfold ProverRwP6BodyCandidate.selected ProverRwP6BoundaryInstall.selected
    rfl
  rw [entry]
  exact ProverRwDictionaryOption.residual_none ops T

theorem primitive_okor [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op7 _ (ProverRwP6BodyCandidate.selected ops) (alloc.vec.Vec U8) verifier.Error
      none verifier.Error.Allocation=ok (.Err .Allocation) := by
  unfold ProverRwP6BodyCandidate.selected ProverRwP6BoundaryInstall.selected
  rfl

theorem actual (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) :
    @PV_RJN_NodeReject.PV_RJN_Producer_NodePrimitives (types base) (selected base heap box ops) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  refine ⟨?_,?_,?_,?_,?_⟩
  · change @ExternalFuns.op235 (types base) (selected base heap box ops)=_
    unfold selected
    rw [PV_B2_F_RawNative.preserved_235]
    exact primitive_bits ops
  · change @ExternalFuns.op236 (types base) (selected base heap box ops)=_
    unfold selected
    rw [PV_B2_F_RawNative.preserved_236]
    exact primitive_batch ops
  · intro T
    change @ExternalFuns.op9 (types base) (selected base heap box ops) T none=_
    unfold selected
    rw [PV_B2_F_RawNative.preserved_9]
    exact primitive_branch ops T
  · intro T
    change @ExternalFuns.op10 (types base) (selected base heap box ops) T none=_
    unfold selected
    rw [PV_B2_F_RawNative.preserved_10]
    exact primitive_residual ops T
  · change @ExternalFuns.op7 (types base) (selected base heap box ops) _ _ none verifier.Error.Allocation=_
    unfold selected
    rw [PV_B2_F_RawNative.preserved_7]
    exact primitive_okor ops
#print axioms primitive_bits
#print axioms primitive_batch
#print axioms primitive_branch
#print axioms primitive_residual
#print axioms primitive_okor
#print axioms actual
end R1Z.PV_RJN_NodeInstalled
