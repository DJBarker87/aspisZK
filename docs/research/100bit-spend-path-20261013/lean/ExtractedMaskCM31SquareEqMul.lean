import ExtractedMaskCM31Square
import ExtractedMaskCM31Mul
import ExtractedMaskSquareArithmetic

/-! Extensional composition showing that the extracted current complex square
and multiplication-by-self return the same CM31 result on canonical inputs.
This remains an operation-level fact, not a caller/refinement theorem. -/
set_option autoImplicit false

namespace AspisR1.ExtractedMaskCM31SquareEqMul

open Aeneas.Std

abbrev CM := AspisR1.ExtractedMaskCM31Square.CM
abbrev M31 := AspisR1.ExtractedMaskCM31Square.M31
abbrev P := AspisR1.ExtractedMaskCM31Square.P

private theorem word_eq_of_value_eq {x y : M31} (h : x.val = y.val) : x = y := by
  exact UScalar.val_eq_imp x y h

theorem current_square_eq_mul_self (x : CM)
    (hx : AspisR1.ExtractedMaskTowerAdd.CanonicalCM x) :
    AspisR1SelectedMaskProbe.field.CM31.square x =
      AspisR1SelectedMaskProbe.field.CM31.mul x x := by
  obtain ⟨s, hs, hsc, hsr, hsi⟩ :=
    AspisR1.ExtractedMaskCM31Square.current_square_words x hx
  obtain ⟨m, hm, hmc, hmr, hmi⟩ :=
    AspisR1.ExtractedMaskCM31Mul.current_mul_words x x hx hx
  have hreal : s.a.val = m.a.val := by
    rw [hsr, hmr, AspisR1.ExtractedMaskCM31Mul.realWord]
    exact AspisR1.ExtractedMaskSquareArithmetic.square_real_word_eq_mul_self_real
      x.a.val x.b.val hx.1 hx.2
  have himag : s.b.val = m.b.val := by
    rw [hsi, hmi]
    have hsq : ((x.a.val * x.b.val) % P +
        (x.a.val * x.b.val) % P) % P =
        (x.a.val * x.b.val + x.a.val * x.b.val) % P :=
      (Nat.add_mod _ _ P).symm
    have hmul : AspisR1.ExtractedMaskCM31Mul.imagWord
        x.a.val x.b.val x.a.val x.b.val =
        (x.a.val * x.b.val + x.b.val * x.a.val) % P := by
      change AspisR1.ExtractedMaskSquareArithmetic.imagWord
        x.a.val x.b.val x.a.val x.b.val = _
      exact AspisR1.ExtractedMaskSquareArithmetic.imagWord_mod
        x.a.val x.b.val x.a.val x.b.val
    rw [hmul, hsq]
    simp [Nat.mul_comm]
  have hsame : s = m := by
    cases s with
    | mk a b =>
      cases m with
      | mk c d =>
        have ea : a = c := word_eq_of_value_eq hreal
        have eb : b = d := word_eq_of_value_eq himag
        cases ea
        cases eb
        rfl
  rw [hs, hm, hsame]

#print axioms current_square_eq_mul_self

end AspisR1.ExtractedMaskCM31SquareEqMul
