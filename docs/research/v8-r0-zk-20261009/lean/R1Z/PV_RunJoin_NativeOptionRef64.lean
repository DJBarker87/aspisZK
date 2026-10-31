import R1Z.PV_RunJoin_NativeFrames63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeOptionRef64
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) :
    @ExternalFuns.op6 (types base) (opsNative base heap box ops runtime world)=
      @ProverRwSuccessOptions.asRef := by
  unfold opsNative PV_RunJoin_WeightInstalled46.selected
  rw [PV_B2_F_RawNative.preserved_6]
  unfold ProverRwP6BodyCandidate.selected ProverRwP6BoundaryInstall.selected
  rfl

#print axioms complete
end R1Z.PV_RunJoin_NativeOptionRef64
