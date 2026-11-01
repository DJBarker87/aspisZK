import R1Z.PV_RunJoin_NativeActual63
import R1Z.PV_RunJoin_MaskTotal69
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeMaskValueTotal69
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected

theorem source {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) :
    @ExternalFuns.op117 (types base) (opsNative base heap box ops runtime world)=
      PV_B3_Install117.callback := by
  unfold opsNative PV_RunJoin_WeightInstalled46.selected
  rw [PV_B2_F_RawNative.preserved_117]
  unfold ProverRwP6BodyCandidate.selected ProverRwP6BoundaryInstall.selected
  rfl

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (c1 : Array aspis_core.field.QM31 16#usize)
    (mask : Array aspis_core.field.QM31 10#usize) (g : aspis_core.field.QM31)
    (point : Array aspis_core.field.QM31 10#usize) :
    ∃ out,@aspis_core.state_only_hiding.state_only_selected_mask_value (types base)
      (opsNative base heap box ops runtime world) c1 mask g point=ok out := by
  change ∃ out,@ExternalFuns.op117 (types base) (opsNative base heap box ops runtime world)
    c1 mask g point=ok out
  rw [source]
  obtain ⟨out,ho⟩ := PV_RunJoin_MaskTotal69.complete (PV_B3_Carrier117.fromArray c1)
    (PV_B3_Carrier117.fromArray mask) (PV_B3_Carrier117.fromQ g) (PV_B3_Carrier117.fromArray point)
  exact ⟨PV_B3_Carrier117.toQ out,by simp only [PV_B3_Install117.callback,ho,PV_B3_Carrier117.map]⟩

#print axioms source
#print axioms complete
end R1Z.PV_RunJoin_NativeMaskValueTotal69
