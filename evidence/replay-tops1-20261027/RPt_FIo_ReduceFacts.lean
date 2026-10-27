import RPt_FIo_ScalarBridge
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.FIo_ReduceFacts

theorem low (x : U64) : (x &&& (2147483647#u64)).val ≤ 2147483647 := by
  change (x.bv &&& (2147483647 : BitVec 64)).toNat ≤2147483647
  rw [BitVec.toNat_and]
  exact Nat.and_le_right

theorem shr31 (x : U64) : x >>> (31#u32)=ok (U64.wrapping_shr x (31#u32)) := by
  simp only [HShiftRight.hShiftRight,UScalar.shiftRight_UScalar,UScalar.shiftRight,
    U64.wrapping_shr,UScalar.wrapping_shr]
  rfl

#print axioms low
#print axioms shr31
end AspisR1.FIo_ReduceFacts
