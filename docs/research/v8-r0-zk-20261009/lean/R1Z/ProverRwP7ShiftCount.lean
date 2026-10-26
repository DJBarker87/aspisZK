import Aeneas
set_option autoImplicit false
namespace R1Z.ProverRwP7ShiftCount
open Aeneas Aeneas.Std
-- The existing wrapping-shift API takes U32 counts. Narrowing a Usize count
-- preserves every masked bit used by a32-bit or64-bit machine shift.
theorem mod32 (n : Usize) : (UScalar.cast .U32 n).val % 32 = n.val % 32 := by
  rw [UScalar.cast_val_eq]
  change (n.val % 4294967296)%32=n.val%32
  exact Nat.mod_mod_of_dvd n.val (by decide : 32 ∣ 4294967296)
theorem mod64 (n : Usize) : (UScalar.cast .U32 n).val % 64 = n.val % 64 := by
  rw [UScalar.cast_val_eq]
  change (n.val % 4294967296)%64=n.val%64
  exact Nat.mod_mod_of_dvd n.val (by decide : 64 ∣ 4294967296)
#print axioms mod32
#print axioms mod64
end R1Z.ProverRwP7ShiftCount
