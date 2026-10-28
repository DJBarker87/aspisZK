import R1Z.PV_AL_TypenumSize
open Aeneas Aeneas.Std Result
namespace R1Z.PV_AL_TypenumValue
set_option autoImplicit false

/-- Project the size recurrence before simplifying any other trait fields. -/
def value : Nat → Result Usize
  | 0 => ok ((UScalar.cast .Usize 1#u8) ||| Usize.wrapping_shl 0#usize 1#u32)
  | k+1 => do
    let n ← value k
    ok ((UScalar.cast .Usize 0#u8) ||| Usize.wrapping_shl n 1#u32)

def rawValue (width : Nat) : Nat → BitVec width
  | 0 => BitVec.setWidth width (BitVec.ofNat 8 1) |||
      (BitVec.ofNat width 0).shiftLeft (1 % width)
  | k+1 => BitVec.setWidth width (BitVec.ofNat 8 0) |||
      (rawValue width k).shiftLeft (1 % width)

theorem raw64 (width : Nat) (h : width=32 ∨ width=64) :
    rawValue width 6=BitVec.ofNat width 64 := by
  rcases h with rfl | rfl <;> decide

theorem value64 : value 6=ok 64#usize := by
  simp only [value,bind_tc_ok]
  congr 1
  bvify System.Platform.numBits
  exact raw64 System.Platform.numBits System.Platform.numBits_eq

#print axioms value
#print axioms rawValue
#print axioms raw64
#print axioms value64
end R1Z.PV_AL_TypenumValue
