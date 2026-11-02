import PV_EVH_NativeZeroWrappers
set_option autoImplicit false
noncomputable section
namespace PV_EVH_NativeEntropyBorrow
open Aeneas Aeneas.Std ProverRwFull
open R1Z.PV_RunJoin_NativeResidual62

/-- Actual emitted array AsMut dictionary after native wrapper installation.
The returned continuation is the array's original mutable restoration. -/
theorem array_borrow (base : ExternalTypes)
    (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
    (box : R1Z.PV_RunJoin_WeightInstalled46.Box) (ops : @ExternalFuns (types base)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)
    ∀ (n : Usize) (a : Array U8 n),
      zeroize.Zeroizing.Insts.CoreConvertAsMut.as_mut
        (Array.Insts.CoreConvertAsMutSlice U8 n)
        (Array.Insts.ZeroizeZeroize n
          (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) a =
        .ok (Array.to_slice_mut a) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box (PV_EVH_ZeroWrappers.selected ops)
  intro n a
  rw [PV_EVH_NativeZeroWrappers.borrow_native base heap box ops]
  rfl

theorem restore_array (n : Usize) (before after : Array U8 n) :
    (Array.to_slice_mut before).2 (Array.to_slice_mut after).1 = after := by
  apply Subtype.ext
  simp [Array.to_slice_mut,Array.from_slice,Array.to_slice,after.property]

#print axioms array_borrow
#print axioms restore_array
end PV_EVH_NativeEntropyBorrow
