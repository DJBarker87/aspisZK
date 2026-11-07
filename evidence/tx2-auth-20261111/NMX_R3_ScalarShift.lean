import NMX_R3_LongBits
set_option autoImplicit false
namespace NMX_R3_ScalarShift
open Aeneas Aeneas.Std Result NMX_R3_ByteCarrier

def tag (next : U64) (i : Usize) : U64 := ⟨next.bv >>> i.val⟩

theorem raw (next : U64) (i : Usize) (index : i.val < 20) :
 next >>> i = ok (tag next i) := by
 change (if i.val < 64 then ok (tag next i) else fail .integerOverflow) = ok (tag next i)
 rw [if_pos (show i.val < 64 by omega)]

theorem represented (next : U64) (i : Usize) (index : i.val < 20) :
 long (tag next i) = long next >>> UInt64.ofNat i.val := by
 apply UInt64.toNat_inj.mp
 have cast : (UInt64.ofNat i.val).toNat = i.val :=
  UInt64.toNat_ofNat_of_lt' (by change i.val < 18446744073709551616; omega)
 rw [UInt64.toNat_shiftRight, long_value, long_value, cast,
  Nat.mod_eq_of_lt (show i.val < 64 by omega)]
 change (next.bv >>> i.val).toNat = next.bv.toNat >>> i.val
 simp only [BitVec.toNat_ushiftRight]

theorem mask_map (x : U64) : long (x &&& 1#u64) = long x &&& 1 := by
 apply UInt64.toBitVec_inj.mp
 rw [NMX_R3_LongBits.value]
 change (x.bv &&& 1#64) = ((long x).toBitVec &&& 1#64)
 rw [NMX_R3_LongBits.value]

theorem mask (x : U64) : x &&& 1#u64 = 0#u64 ↔ long x &&& 1 = 0 := by
 constructor
 · intro h
   rw [← mask_map, h]
   rfl
 · intro h
   apply NMX_R3_LongBits.injective
   rw [mask_map, h]
   rfl
#print axioms raw
#print axioms represented
#print axioms mask_map
#print axioms mask
end NMX_R3_ScalarShift
