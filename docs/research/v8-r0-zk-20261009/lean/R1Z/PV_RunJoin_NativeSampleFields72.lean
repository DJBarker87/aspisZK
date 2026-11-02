import R1Z.PV_RunJoin_NativeQuarticTotal69
import R1Z.PV_RunJoin_SampleSource34
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeSampleFields72
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
variable {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)

theorem one : @aspis_core.field.QM31.ONE (types base) (opsNative base heap box ops runtime world)=
    @aspis_core.field.QM31.ONE (types base) (ProverRwDictionaryScalar.selected ops) := by
  change @ExternalFuns.op65 (types base) (opsNative base heap box ops runtime world)=_
  unfold opsNative PV_RunJoin_WeightInstalled46.selected
  rw [PV_B2_F_RawNative.preserved_65]
  unfold ProverRwP6BodyCandidate.selected ProverRwP6BoundaryInstall.selected
  rfl

theorem complex : @aspis_core.field.CM31.from_m31 (types base) (opsNative base heap box ops runtime world)=
    @aspis_core.field.CM31.from_m31 (types base) (ProverRwDictionaryScalar.selected ops) := by
  change @ExternalFuns.op61 (types base) (opsNative base heap box ops runtime world)=_
  unfold opsNative PV_RunJoin_WeightInstalled46.selected
  rw [PV_B2_F_RawNative.preserved_61]
  unfold ProverRwP6BodyCandidate.selected ProverRwP6BoundaryInstall.selected
  rfl

theorem quartic : @aspis_core.field.QM31.from_cm31 (types base) (opsNative base heap box ops runtime world)=
    @aspis_core.field.QM31.from_cm31 (types base) (ProverRwDictionaryScalar.selected ops) := by
  change @ExternalFuns.op66 (types base) (opsNative base heap box ops runtime world)=_
  unfold opsNative PV_RunJoin_WeightInstalled46.selected
  rw [PV_B2_F_RawNative.preserved_66]
  unfold ProverRwP6BodyCandidate.selected ProverRwP6BoundaryInstall.selected
  rfl

#print axioms one
#print axioms complex
#print axioms quartic
end R1Z.PV_RunJoin_NativeSampleFields72
