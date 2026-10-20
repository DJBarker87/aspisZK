import CuSavingsS2SourceTables
set_option autoImplicit false
namespace AspisR1.CuSavingsS2MaskBits

theorem partial_step (m s : Nat) :
    (if m.testBit s then (m%2^s) ||| 2^s else m%2^s) = m%2^(s+1) := by
  cases hb : m.testBit s <;>
    simp only [hb,Bool.false_eq_true,if_false,if_true] <;>
    apply Nat.eq_of_testBit_eq <;> intro i <;>
    by_cases he : i=s
  all_goals try (subst i;simp [Nat.testBit_or,Nat.testBit_two_pow,Nat.testBit_mod_two_pow,hb])
  all_goals
    have hne : s ≠ i := by omega
    by_cases hi : i<s
    · have hi1 : i<s+1 := by omega
      simp [Nat.testBit_or,Nat.testBit_two_pow,Nat.testBit_mod_two_pow,hne,hi,hi1]
    · have hi1 : ¬ i<s+1 := by omega
      simp [Nat.testBit_or,Nat.testBit_two_pow,Nat.testBit_mod_two_pow,hne,hi,hi1]

#print axioms partial_step
end AspisR1.CuSavingsS2MaskBits
