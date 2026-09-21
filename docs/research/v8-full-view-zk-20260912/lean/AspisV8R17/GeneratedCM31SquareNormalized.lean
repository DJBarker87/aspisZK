import AspisV8R17.GeneratedCM31Square
import AspisV8R17.GeneratedCM31Normalized

namespace AspisV8R17.GeneratedCM31SquareNormalized
open Aeneas.Std V7Tag73CurrentHelpersOpaque RawReducer GeneratedCM31Square

theorem square_real_int (a b : Nat) (hb : b < P) :
    ((((a+b)*(a+P-b))%P : Nat) : Int) =
      ((a : Int)*a - (b : Int)*b) % (P : Int) := by
  rw [← Int.natCast_mul, ← Int.natCast_mul]
  have hbb := Nat.mul_le_mul_right b (Nat.le_of_lt hb)
  unfold P at *
  simp only [Nat.mul_sub_left_distrib, Nat.add_mul, Nat.mul_add,
    Nat.mul_comm b a]
  omega

theorem square_imag_mod (a b : Nat) :
    ((a*b)%P + (a*b)%P)%P = (a*b+a*b)%P := by
  unfold P
  omega

theorem generated_square_complex_residues (x : aspis_core.field.CM31)
    (ha : x.a.val < P) (hb : x.b.val < P) :
    ∃ z : aspis_core.field.CM31, aspis_core.field.CM31.square x = .ok z ∧
      (z.a.val : Int) = ((x.a.val : Int)*x.a.val - (x.b.val : Int)*x.b.val) % (P : Int) ∧
      z.b.val = (x.a.val*x.b.val+x.a.val*x.b.val)%P ∧
      z.a.val < P ∧ z.b.val < P := by
  obtain ⟨z, hz, hr, hi, hca, hcb⟩ := generated_square_words x ha hb
  refine ⟨z, hz, ?_, ?_, hca, hcb⟩
  · rw [hr]
    exact square_real_int _ _ hb
  · rw [hi]
    exact square_imag_mod _ _

private theorem word_eq_of_value_eq {x y : U32} (h : x.val = y.val) : x = y := by
  cases x with
  | mk x =>
    cases y with
    | mk y =>
      congr 1
      exact BitVec.eq_of_toNat_eq h

theorem generated_square_eq_mul_self (x : aspis_core.field.CM31)
    (ha : x.a.val < P) (hb : x.b.val < P) :
    aspis_core.field.CM31.square x = aspis_core.field.CM31.mul x x := by
  obtain ⟨s, hs, hsr, hsi, _, _⟩ := generated_square_complex_residues x ha hb
  obtain ⟨m, hm, hmr, hmi, _, _⟩ :=
    GeneratedCM31Normalized.generated_mul_complex_residues x x ha hb ha hb
  have real_eq : s.a.val = m.a.val := by omega
  have imag_eq : s.b.val = m.b.val := by
    rw [hsi, hmi, Nat.mul_comm x.b.val x.a.val]
  have same : s = m := by
    cases s with
    | mk a b =>
      cases m with
      | mk c d =>
        have ea : a = c := word_eq_of_value_eq real_eq
        have eb : b = d := word_eq_of_value_eq imag_eq
        cases ea
        cases eb
        rfl
  rw [hs, hm, same]

#print axioms square_real_int
#print axioms square_imag_mod
#print axioms generated_square_complex_residues
#print axioms generated_square_eq_mul_self
end AspisV8R17.GeneratedCM31SquareNormalized
