import AspisV8R17.GeneratedCM31Mul

/-! Standard complex-product residues for the current checked source execution.
Real subtraction is in Int, not truncated Nat subtraction. No field-algebra
tactic aggregate is needed for these fixed-modulus congruences. -/
namespace AspisV8R17.GeneratedCM31Normalized
open Aeneas.Std V7Tag73CurrentHelpersOpaque GeneratedCM31Mul RawReducer

theorem realWord_int (a b c d : Nat) :
    (realWord a b c d : Int) = ((a : Int)*c - (b : Int)*d) % (P : Int) := by
  rw [← Int.natCast_mul, ← Int.natCast_mul]
  unfold realWord P
  omega

theorem imagWord_mod (a b c d : Nat) :
    imagWord a b c d = (a*d+b*c)%P := by
  unfold imagWord P
  simp only [Nat.add_mul, Nat.mul_add]
  omega

theorem generated_mul_complex_residues (x y : aspis_core.field.CM31)
    (ha : x.a.val < P) (hb : x.b.val < P)
    (hc : y.a.val < P) (hd : y.b.val < P) :
    ∃ z : aspis_core.field.CM31, aspis_core.field.CM31.mul x y = .ok z ∧
      (z.a.val : Int) = ((x.a.val : Int)*y.a.val - (x.b.val : Int)*y.b.val) % (P : Int) ∧
      z.b.val = (x.a.val*y.b.val + x.b.val*y.a.val)%P ∧
      z.a.val < P ∧ z.b.val < P := by
  obtain ⟨z, hz, hr, hi, hca, hcb⟩ := generated_mul_words x y ha hb hc hd
  refine ⟨z, hz, ?_, ?_, hca, hcb⟩
  · rw [hr]
    exact realWord_int _ _ _ _
  · rw [hi]
    exact imagWord_mod _ _ _ _

#print axioms realWord_int
#print axioms imagWord_mod
#print axioms generated_mul_complex_residues
end AspisV8R17.GeneratedCM31Normalized
