import Mathlib

/-! Exact little-endian OR/shift index assembly used by the selected
recovered-witness decoder. Generic bit recurrences are proved before the
20-bit specialization; no enumeration of concrete field/domain values. -/
set_option autoImplicit false
namespace AspisV8.DecodedIndex32

def assemble (bits : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n+1 => assemble bits n ||| (bits n).toNat <<< n

theorem shifted_bit_test (bit : Bool) (shift position : Nat) :
    (bit.toNat <<< shift).testBit position=if position=shift then bit else false := by
  rw [Nat.testBit_shiftLeft,Nat.testBit_bool_toNat]
  by_cases equal : position=shift
  · subst position
    simp
  · by_cases below : position<shift
    · have notAbove : ¬position≥shift := by omega
      simp [equal,notAbove]
    · have above : position≥shift := by omega
      have difference : position-shift≠0 := by omega
      simp [equal,above,difference]

theorem assemble_testBit (bits : Nat → Bool) (n position : Nat) :
    (assemble bits n).testBit position=if position<n then bits position else false := by
  induction n with
  | zero => simp [assemble]
  | succ n ih =>
    rw [assemble,Nat.testBit_or,ih,shifted_bit_test]
    by_cases below : position<n
    · have different : position≠n := by omega
      have belowNext : position<n+1 := by omega
      simp [below,different,belowNext]
    · by_cases equal : position=n
      · subst position
        simp
      · have notNext : ¬position<n+1 := by omega
        simp [below,equal,notNext]

theorem shifted_bit_bound (bit : Bool) (n : Nat) : bit.toNat <<< n<2^(n+1) := by
  have positive:=Nat.two_pow_pos n
  cases bit <;> simp only [Bool.toNat_false,Bool.toNat_true,Nat.shiftLeft_eq,zero_mul,one_mul]
  all_goals rw [pow_succ]; omega

theorem assemble_bound (bits : Nat → Bool) (n : Nat) : assemble bits n<2^n := by
  induction n with
  | zero => simp [assemble]
  | succ n ih =>
    apply Nat.or_lt_two_pow
    · have positive:=Nat.two_pow_pos n
      rw [pow_succ]
      omega
    · exact shifted_bit_bound _ _

/-- The literal machine-width recurrence, including the same bitwise OR,
Bool-to-u32 cast and left shift. UInt32 shift counts are masked by32;
the theorem below proves the selected counts never reach that boundary. -/
def assemble32 (bits : Nat → Bool) : Nat → UInt32
  | 0 => 0
  | n+1 => assemble32 bits n ||| UInt32.ofNat (bits n).toNat <<< UInt32.ofNat n

theorem uint32_shift_is_exact (bit : Bool) (n : Nat) (hn : n<32) :
    (UInt32.ofNat bit.toNat <<< UInt32.ofNat n).toNat=bit.toNat <<< n := by
  have bitBound : bit.toNat<2^32 := by cases bit <;> decide
  have nBound : n<2^32 := by omega
  have shiftBound : bit.toNat <<< n<2^32 :=
    lt_of_lt_of_le (shifted_bit_bound bit n) (Nat.pow_le_pow_right (by decide) (by omega))
  rw [UInt32.toNat_shiftLeft,UInt32.toNat_ofNat',UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt bitBound,Nat.mod_eq_of_lt nBound,Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt shiftBound]

theorem assemble32_toNat (bits : Nat → Bool) (n : Nat) (hn : n≤32) :
    (assemble32 bits n).toNat=assemble bits n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [assemble32,UInt32.toNat_or,ih (by omega),uint32_shift_is_exact _ n (by omega)]
    rfl

theorem selected_index_contract (bits : Nat → Bool) :
    (assemble32 bits 20).toNat<2^20 ∧
    (∀ (i : Nat), i < 20 → (assemble32 bits 20).toNat.testBit i = bits i) ∧
    (∀ (i : Nat), 20 ≤ i → (assemble32 bits 20).toNat.testBit i = false) := by
  rw [assemble32_toNat bits 20 (by decide)]
  refine ⟨assemble_bound bits 20,?_,?_⟩
  · intro i hi
    rw [assemble_testBit,if_pos hi]
  · intro i hi
    rw [assemble_testBit,if_neg (by omega)]

#print axioms shifted_bit_test
#print axioms assemble_testBit
#print axioms shifted_bit_bound
#print axioms assemble_bound
#print axioms uint32_shift_is_exact
#print axioms assemble32_toNat
#print axioms selected_index_contract
end AspisV8.DecodedIndex32
