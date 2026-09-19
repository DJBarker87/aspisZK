import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Algebra of the literal source OOD chord. No probability assumptions. -/
set_option autoImplicit false
namespace AspisV8R15.CircleChord
variable {F : Type*} [Field F]

def px (t : F) : F := (1 - t^2) / (1 + t^2)
def py (t : F) : F := 2*t / (1 + t^2)
def chord (t u x y : F) : F :=
  px t * py u - py t * px u + (py t - py u)*x + (px u - px t)*y

theorem rational_factor (t u r : F)
    (ht : 1+t^2 ≠ 0) (hu : 1+u^2 ≠ 0) (hr : 1+r^2 ≠ 0) :
    chord t u (px r) (py r) =
      4*(u-t)*(r-t)*(r-u) / ((1+t^2)*(1+u^2)*(1+r^2)) := by
  unfold chord px py
  field_simp
  ring

theorem exceptional_factor (t u : F)
    (ht : 1+t^2 ≠ 0) (hu : 1+u^2 ≠ 0) :
    chord t u (-1) 0 = 4*(u-t) / ((1+t^2)*(1+u^2)) := by
  unfold chord px py
  field_simp
  ring

theorem rational_nonzero (t u r : F) (h4 : (4 : F) ≠ 0)
    (ht : 1+t^2 ≠ 0) (hu : 1+u^2 ≠ 0) (hr : 1+r^2 ≠ 0)
    (htu : u ≠ t) (hrt : r ≠ t) (hru : r ≠ u) :
    chord t u (px r) (py r) ≠ 0 := by
  rw [rational_factor t u r ht hu hr]
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero h4 (sub_ne_zero.mpr htu))
      (sub_ne_zero.mpr hrt)) (sub_ne_zero.mpr hru))
    (mul_ne_zero (mul_ne_zero ht hu) hr)

theorem exceptional_nonzero (t u : F) (h4 : (4 : F) ≠ 0)
    (ht : 1+t^2 ≠ 0) (hu : 1+u^2 ≠ 0) (htu : u ≠ t) :
    chord t u (-1) 0 ≠ 0 := by
  rw [exceptional_factor t u ht hu]
  exact div_ne_zero (mul_ne_zero h4 (sub_ne_zero.mpr htu)) (mul_ne_zero ht hu)

#print axioms rational_factor
#print axioms exceptional_factor
#print axioms rational_nonzero
#print axioms exceptional_nonzero
end AspisV8R15.CircleChord
