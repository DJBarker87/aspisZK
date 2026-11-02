import R1Z.PV_RunJoin_NativeQuarticTotal69
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_InterpolationFields72
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
variable {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)

theorem op55 : @ExternalFuns.op55 (types base) (opsNative base heap box ops runtime world)=
    @ExternalFuns.op55 (types base) (@ProverRwP6BodyCandidate.selected (types base) (residual base ops runtime world)) := by
  unfold opsNative PV_RunJoin_WeightInstalled46.selected
  exact PV_B2_F_RawNative.preserved_55 (PV_RunJoin_NativeResidual62.baseTypes base) heap box _

#print axioms op55

theorem op56 : @ExternalFuns.op56 (types base) (opsNative base heap box ops runtime world)=
    @ExternalFuns.op56 (types base) (@ProverRwP6BodyCandidate.selected (types base) (residual base ops runtime world)) := by
  unfold opsNative PV_RunJoin_WeightInstalled46.selected
  exact PV_B2_F_RawNative.preserved_56 (PV_RunJoin_NativeResidual62.baseTypes base) heap box _

#print axioms op56

theorem op57 : @ExternalFuns.op57 (types base) (opsNative base heap box ops runtime world)=
    @ExternalFuns.op57 (types base) (@ProverRwP6BodyCandidate.selected (types base) (residual base ops runtime world)) := by
  unfold opsNative PV_RunJoin_WeightInstalled46.selected
  exact PV_B2_F_RawNative.preserved_57 (PV_RunJoin_NativeResidual62.baseTypes base) heap box _

#print axioms op57

theorem op59 : @ExternalFuns.op59 (types base) (opsNative base heap box ops runtime world)=
    @ExternalFuns.op59 (types base) (@ProverRwP6BodyCandidate.selected (types base) (residual base ops runtime world)) := by
  unfold opsNative PV_RunJoin_WeightInstalled46.selected
  exact PV_B2_F_RawNative.preserved_59 (PV_RunJoin_NativeResidual62.baseTypes base) heap box _

#print axioms op59

theorem op64 : @ExternalFuns.op64 (types base) (opsNative base heap box ops runtime world)=
    @ExternalFuns.op64 (types base) (@ProverRwP6BodyCandidate.selected (types base) (residual base ops runtime world)) := by
  unfold opsNative PV_RunJoin_WeightInstalled46.selected
  exact PV_B2_F_RawNative.preserved_64 (PV_RunJoin_NativeResidual62.baseTypes base) heap box _

#print axioms op64

theorem op67 : @ExternalFuns.op67 (types base) (opsNative base heap box ops runtime world)=
    @ExternalFuns.op67 (types base) (@ProverRwP6BodyCandidate.selected (types base) (residual base ops runtime world)) := by
  unfold opsNative PV_RunJoin_WeightInstalled46.selected
  exact PV_B2_F_RawNative.preserved_67 (PV_RunJoin_NativeResidual62.baseTypes base) heap box _

#print axioms op67

theorem op70 : @ExternalFuns.op70 (types base) (opsNative base heap box ops runtime world)=
    @ExternalFuns.op70 (types base) (@ProverRwP6BodyCandidate.selected (types base) (residual base ops runtime world)) := by
  unfold opsNative PV_RunJoin_WeightInstalled46.selected
  exact PV_B2_F_RawNative.preserved_70 (PV_RunJoin_NativeResidual62.baseTypes base) heap box _

#print axioms op70

theorem op73 : @ExternalFuns.op73 (types base) (opsNative base heap box ops runtime world)=
    @ExternalFuns.op73 (types base) (@ProverRwP6BodyCandidate.selected (types base) (residual base ops runtime world)) := by
  unfold opsNative PV_RunJoin_WeightInstalled46.selected
  exact PV_B2_F_RawNative.preserved_73 (PV_RunJoin_NativeResidual62.baseTypes base) heap box _

#print axioms op73

theorem op74 : @ExternalFuns.op74 (types base) (opsNative base heap box ops runtime world)=
    @ExternalFuns.op74 (types base) (@ProverRwP6BodyCandidate.selected (types base) (residual base ops runtime world)) := by
  unfold opsNative PV_RunJoin_WeightInstalled46.selected
  exact PV_B2_F_RawNative.preserved_74 (PV_RunJoin_NativeResidual62.baseTypes base) heap box _

#print axioms op74
end R1Z.PV_RunJoin_InterpolationFields72
