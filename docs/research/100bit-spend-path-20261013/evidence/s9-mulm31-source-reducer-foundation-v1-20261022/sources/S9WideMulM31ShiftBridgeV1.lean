import Aeneas

set_option autoImplicit false
open Aeneas Aeneas.Std

namespace AspisR1S9WideMulM31ShiftBridgeV1

/-- The source `wrapping_shr` operation at the reducer's literal shift amount
is exactly the bitvector shift used by the operational R22 reducer model. -/
theorem wrapping_shr31_eq_bitvector (x : Std.U64) :
    Std.U64.wrapping_shr x 31#u32 = ⟨x.bv.ushiftRight 31⟩ := by
  apply UScalar.eq_of_val_eq
  change (Std.U64.wrapping_shr x 31#u32).bv.toNat =
    (x.bv.ushiftRight 31).toNat
  rw [Std.U64.wrapping_shr_bv_eq]
  rfl

#print axioms wrapping_shr31_eq_bitvector

end AspisR1S9WideMulM31ShiftBridgeV1
