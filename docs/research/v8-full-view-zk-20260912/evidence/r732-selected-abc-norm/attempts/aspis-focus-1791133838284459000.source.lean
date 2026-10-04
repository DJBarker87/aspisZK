import Mathlib.Tactic

set_option autoImplicit false
namespace AspisV8R19.R732SelectedAbcNorm
variable {F : Type*} [Field F] [NeZero (2 : F)]

theorem selected_abc_norm_ne_zero (x0 y0 x1 y1 : F)
    (h0 : x0^2 + y0^2 = 1) (h1 : x1^2 + y1^2 = 1)
    (hx : x1 - x0 ≠ 0) :
    (y0 - y1)^2 + (x1 - x0)^2 ≠ 0 := by
  intro hn
  have hdot2 : (2 : F) * (x0 * x1 + y0 * y1 - 1) = 0 := by
    linear_combination h0 + h1 - hn
  have hdot : x0 * x1 + y0 * y1 = 1 := by
    have hzero : x0 * x1 + y0 * y1 - 1 = 0 :=
      (mul_eq_zero.mp hdot2).resolve_left (NeZero.ne 2)
    exact sub_eq_zero.mp hzero
  let area : F := x0 * y1 - y0 * x1
  have hsum : area^2 + (x0 * x1 + y0 * y1)^2 =
      (x0^2 + y0^2) * (x1^2 + y1^2) := by
    dsimp [area]
    ring
  have harea_sum : area^2 + 1 = 1 := by
    calc
      area^2 + 1 = area^2 + (x0 * x1 + y0 * y1)^2 := by rw [hdot]
      _ = (x0^2 + y0^2) * (x1^2 + y1^2) := hsum
      _ = 1 := by rw [h0, h1]; ring
  have harea2 : area^2 = 0 := by
    linear_combination harea_sum
  have harea : area = 0 := by
    apply mul_self_eq_zero.mp
    simpa only [pow_two] using harea2
  have hcoordinate : x0 * (x0 * x1 + y0 * y1) - y0 * area =
      x1 * (x0^2 + y0^2) := by
    dsimp [area]
    ring
  have heq : x1 = x0 := by
    calc
      x1 = x1 * (x0^2 + y0^2) := by rw [h0, mul_one]
      _ = x0 * (x0 * x1 + y0 * y1) - y0 * area := hcoordinate.symm
      _ = x0 := by rw [hdot, harea]; ring
  apply hx
  rw [heq]
  ring

#print axioms selected_abc_norm_ne_zero
end AspisV8R19.R732SelectedAbcNorm
