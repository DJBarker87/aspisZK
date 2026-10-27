import R1Z.PV_Op134_Order
namespace R1Z.PV_Op134_Index
set_option autoImplicit false

theorem shift (row : Nat) : row >>> 4 = row / 16 := by
  simpa only [Nat.shiftRight_eq_div_pow] using (rfl : row / 2^4 = row / 16)

theorem low_bits (row : Nat) : row &&& 15 = row % 16 := by
  simpa only [show 2^4 = (16 : Nat) from rfl, show (16 : Nat)-1=15 from rfl]
    using Nat.and_two_pow_sub_one_eq_mod row 4

theorem bounds (row : Nat) (hr : row < 1024) :
    row / 16 < 64 ∧ row % 16 < 16 ∧ 16*(row/16)+row%16=row := by omega

theorem reconstruct (block bit : Nat) (hb : block < 64) (hi : bit < 16) :
    16*block+bit < 1024 ∧ (16*block+bit)/16=block ∧ (16*block+bit)%16=bit := by omega

theorem coordinate_injective {a b : Nat}
    (hq : a/16=b/16) (hr : a%16=b%16) : a=b := by omega
#print axioms shift
#print axioms low_bits
#print axioms bounds
#print axioms reconstruct
#print axioms coordinate_injective
end R1Z.PV_Op134_Index
