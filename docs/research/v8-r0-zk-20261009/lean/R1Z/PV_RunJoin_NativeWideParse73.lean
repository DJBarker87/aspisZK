import R1Z.PV_RunJoin_WideWireParse73
import R1Z.PV_RunJoin_NativeQuarticTotal69
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeWideParse73
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
abbrev W := aspis_core.field.wide_exact.WideExact
variable {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)

theorem source : @aspis_core.field.wide_exact.WideExact.from_le_bytes (types base)
    (opsNative base heap box ops runtime world)=ProverRwDictionaryBytesSource.aspis_core.field.wide_exact.WideExact.from_le_bytes := by
  change @ExternalFuns.op50 (types base) (opsNative base heap box ops runtime world)=_
  unfold opsNative PV_RunJoin_WeightInstalled46.selected
  rw [PV_B2_F_RawNative.preserved_50]
  unfold ProverRwP6BodyCandidate.selected ProverRwP6BoundaryInstall.selected
  rfl

theorem complete (x : W) (canonical : PV_RunJoin_WideLimbsParse72.Canonical x) :
    @aspis_core.field.wide_exact.WideExact.from_le_bytes (types base)
      (opsNative base heap box ops runtime world) (Array.to_slice (PV_RunJoin_FlatBytes35.wire x))=ok (some x) := by
  rw [source]
  exact PV_RunJoin_WideWireParse73.complete x canonical

theorem c1 (x : W) : @aspis_core.field.wide_exact.WideExact.impl.c1 (types base)
    (opsNative base heap box ops runtime world) x=ok x.c1 := by
  change @ExternalFuns.op44 (types base) (opsNative base heap box ops runtime world) x=_
  unfold opsNative PV_RunJoin_WeightInstalled46.selected
  rw [PV_B2_F_RawNative.preserved_44]
  unfold ProverRwP6BodyCandidate.selected ProverRwP6BoundaryInstall.selected
  rfl

#print axioms source
#print axioms complete
#print axioms c1
end R1Z.PV_RunJoin_NativeWideParse73
