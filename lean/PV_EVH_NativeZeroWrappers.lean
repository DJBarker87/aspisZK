import PV_EVH_NativeZeroInstall
import PV_EVH_ZeroWrappers
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeZeroWrappers
open Aeneas Aeneas.Std ProverRwFull
open R1Z.PV_RunJoin_NativeResidual62

/-- Each wrapper is installed through the actual opsNative selector. Remaining
residual operations are still explicit; no whole-entry adequacy is inferred. -/
theorem wrappers_native (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    let selected := @PV_EVH_ZeroWrappers.selected (types base) ops
    (opsNative base heap box selected).op125 = @PV_EVH_ZeroWrappers.asMut ∧
    (opsNative base heap box selected).op126 = @PV_EVH_ZeroWrappers.derefMut ∧
    (opsNative base heap box selected).op127 = @PV_EVH_ZeroWrappers.deref ∧
    (opsNative base heap box selected).op128 = @PV_EVH_ZeroWrappers.new ∧
    (opsNative base heap box selected).op130 = @PV_EVH_ZeroWrappers.zeroize ∧
    (opsNative base heap box selected).op131 = @PV_EVH_ZeroWrappers.asRef := by
  dsimp only
  unfold opsNative R1Z.PV_RunJoin_WeightInstalled46.selected
  rw [PV_B2_F_RawNative.preserved_125,PV_B2_F_RawNative.preserved_126,
    PV_B2_F_RawNative.preserved_127,PV_B2_F_RawNative.preserved_128,
    PV_B2_F_RawNative.preserved_130,PV_B2_F_RawNative.preserved_131]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem constructor_native (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)
    ∀ {Z : Type} (d : zeroize.Zeroize Z) (z : Z),
      zeroize.Zeroizing.new d z = .ok z := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)
  intro Z d z
  change (opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)).op128 d z = _
  rw [(wrappers_native base heap box ops).2.2.2.1]
  rfl

theorem borrow_native (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)
    ∀ {T Z : Type} (d : core.convert.AsMut Z T) (dz : zeroize.Zeroize Z) (z : Z),
      zeroize.Zeroizing.Insts.CoreConvertAsMut.as_mut d dz z = d.as_mut z := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)
  intro T Z d dz z
  change (opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)).op125 d dz z = _
  rw [(wrappers_native base heap box ops).1]
  rfl

theorem array_native (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)
    ∀ (n : Usize) (a : Array U8 n),
      (Array.Insts.ZeroizeZeroize n
        (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)).zeroize a =
      .ok (Array.repeat n 0#u8) :=
  PV_EVH_NativeZeroInstall.array_value_native base heap box (PV_EVH_ZeroWrappers.selected ops)

#print axioms wrappers_native
#print axioms constructor_native
#print axioms borrow_native
#print axioms array_native
end PV_EVH_NativeZeroWrappers
