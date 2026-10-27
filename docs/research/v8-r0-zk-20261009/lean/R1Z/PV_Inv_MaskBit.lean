import R0P.Copy
set_option autoImplicit false
namespace R1Z.PV_Inv_MaskBit

theorem source_shift (bit : Nat) : (1 : Nat) <<< bit = 2^bit := by rw [Nat.shiftLeft_eq,one_mul]

theorem insert_bit (mask bit query : Nat) :
    (mask ||| (2^bit)).testBit query = (mask.testBit query || decide (bit=query)) := by
  rw [Nat.testBit_or,Nat.testBit_two_pow]

#print axioms source_shift
#print axioms insert_bit
end R1Z.PV_Inv_MaskBit
