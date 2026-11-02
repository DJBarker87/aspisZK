import PV_EVH_NativeOperators
import PV_EVH_ZeroAddressBridge
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeZeroBoundary
open Aeneas Aeneas.Std ProverRwFull
open R1Z.PV_RunJoin_NativeResidual62

/-- The actual native selector preserves these residual dictionary entries.
Selection alone does not supply either the byte value law or physical effects. -/
theorem array_residual (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    @ExternalFuns.op122 (types base) (opsNative base heap box ops) =
      @ExternalFuns.op122 (types base) ops := by
  unfold opsNative R1Z.PV_RunJoin_WeightInstalled46.selected
  rw [PV_B2_F_RawNative.preserved_122]
  rfl

theorem scalar_residual (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    @ExternalFuns.op123 (types base) (opsNative base heap box ops) =
      @ExternalFuns.op123 (types base) ops := by
  unfold opsNative R1Z.PV_RunJoin_WeightInstalled46.selected
  rw [PV_B2_F_RawNative.preserved_123]
  rfl

/-- The extracted source dictionary is precisely Array -> scalar -> op123.
This equation exposes the residual operation at the actual native selection;
it does not install a replacement dictionary or assert zeroize is silent. -/
theorem emitted_array (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops
    ∀ (n : Usize) (a : Array U8 n),
      (Array.Insts.ZeroizeZeroize n
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)).zeroize a =
      ops.op122 (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes) a := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops
  intro n a
  change (opsNative base heap box ops).op122 _ a = _
  rw [array_residual]

theorem emitted_scalar (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops
    ∀ x : U8,
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes).zeroize x =
      ops.op123 U8.Insts.ZeroizeDefaultIsZeroes x := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops
  intro x
  change (opsNative base heap box ops).op123 _ x = _
  rw [scalar_residual]

#print axioms array_residual
#print axioms scalar_residual
#print axioms emitted_array
#print axioms emitted_scalar
end PV_EVH_NativeZeroBoundary
