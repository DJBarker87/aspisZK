import PV_EVH_NativeEntropyBorrow
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeEntropyAccess
open Aeneas Aeneas.Std ProverRwFull
open R1Z.PV_RunJoin_NativeResidual62

theorem deref_native (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)
    ∀ {Z : Type} (d : zeroize.Zeroize Z) (z : Z),
      zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref d z = .ok z := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)
  intro Z d z
  change (opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)).op127 d z = _
  rw [(PV_EVH_NativeZeroWrappers.wrappers_native base heap box ops).2.2.1]
  rfl

/-- The backward continuation is identity on the transparent wrapper, and is
still called with the updated array rather than the original zero array. -/
theorem deref_mut_native (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)
    ∀ {Z : Type} (d : zeroize.Zeroize Z) (z : Z),
      zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut d z = .ok (z,id) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)
  intro Z d z
  change (opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)).op126 d z = _
  rw [(PV_EVH_NativeZeroWrappers.wrappers_native base heap box ops).2.1]
  rfl

#print axioms deref_native
#print axioms deref_mut_native
end PV_EVH_NativeEntropyAccess
