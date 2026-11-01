import R1Z.PV_RunJoin_NativeActual63
import R1Z.ProverRwP6QuarticTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeQuarticTotal69
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
abbrev Q := aspis_core.field.QM31

theorem add_source {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) :
    @aspis_core.field.QM31.add (types base) (opsNative base heap box ops runtime world)=
      ProverRwDictionaryTower.qAdd := by
  change @ExternalFuns.op67 (types base) (opsNative base heap box ops runtime world)=_
  unfold opsNative PV_RunJoin_WeightInstalled46.selected
  rw [PV_B2_F_RawNative.preserved_67]
  unfold ProverRwP6BodyCandidate.selected ProverRwP6BoundaryInstall.selected
  rfl

theorem mul_source {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) :
    @aspis_core.field.QM31.mul (types base) (opsNative base heap box ops runtime world)=
      ProverRwDictionaryTower.qMul := by
  change @ExternalFuns.op69 (types base) (opsNative base heap box ops runtime world)=_
  unfold opsNative PV_RunJoin_WeightInstalled46.selected
  rw [PV_B2_F_RawNative.preserved_69]
  unfold ProverRwP6BodyCandidate.selected ProverRwP6BoundaryInstall.selected
  rfl

theorem zero_source {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) :
    @aspis_core.field.QM31.ZERO (types base) (opsNative base heap box ops runtime world)=
      ok (ProverRwDictionaryTower.fromQ AspisR1ProducerRelease47.field.QM31.ZERO) := by
  change @ExternalFuns.op64 (types base) (opsNative base heap box ops runtime world)=_
  unfold opsNative PV_RunJoin_WeightInstalled46.selected
  rw [PV_B2_F_RawNative.preserved_64]
  unfold ProverRwP6BodyCandidate.selected ProverRwP6BoundaryInstall.selected
  rfl

theorem add {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) (a b : Q) :
    ∃ c, @aspis_core.field.QM31.add (types base) (opsNative base heap box ops runtime world) a b=ok c := by
  rw [add_source]
  obtain ⟨c,hc⟩ := ProverRwP6QuarticTotal.add (ProverRwDictionaryTower.toQ a) (ProverRwDictionaryTower.toQ b)
  exact ⟨ProverRwDictionaryTower.fromQ c,by simp only [ProverRwDictionaryTower.qAdd,hc,ProverRwDictionaryTower.mapResult]⟩

theorem mul {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) (a b : Q) :
    ∃ c, @aspis_core.field.QM31.mul (types base) (opsNative base heap box ops runtime world) a b=ok c := by
  rw [mul_source]
  obtain ⟨c,hc⟩ := ProverRwP6QuarticTotal.mul (ProverRwDictionaryTower.toQ a) (ProverRwDictionaryTower.toQ b)
  exact ⟨ProverRwDictionaryTower.fromQ c,by simp only [ProverRwDictionaryTower.qMul,hc,ProverRwDictionaryTower.mapResult]⟩

#print axioms add_source
#print axioms mul_source
#print axioms zero_source
#print axioms add
#print axioms mul
end R1Z.PV_RunJoin_NativeQuarticTotal69
