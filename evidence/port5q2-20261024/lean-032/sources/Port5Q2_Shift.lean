import Port5Q2_ReaderRaw
set_option autoImplicit false
namespace AspisR1.Port5Q2_Shift
open Aeneas Aeneas.Std

/-- Use BitVec's closed form; do not kernel-reduce a concrete shift graph. -/
theorem eighteen : U32.wrapping_shl 1#u32 18#u32=262144#u32 := by
  apply UScalar.eq_of_val_eq
  change ((1 : BitVec 32) <<< 18).toNat=262144
  rw [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
  norm_num

#print axioms eighteen
end AspisR1.Port5Q2_Shift
