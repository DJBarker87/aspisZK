import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Field.Subfield.Basic

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

theorem recover_denom (x y : F) (hx : 1+x ≠ 0)
    (hc : x^2+y^2=1) : 1+(y/(1+x))^2 = 2/(1+x) := by
  field_simp
  linear_combination hc

theorem recover_point (x y : F) (h2 : (2 : F) ≠ 0)
    (hx : 1+x ≠ 0) (hc : x^2+y^2=1) :
    px (y/(1+x)) = x ∧ py (y/(1+x)) = y := by
  unfold px py
  rw [recover_denom x y hx hc]
  constructor
  · field_simp
    linear_combination -hc
  · field_simp

/-- Every circle point in a subfield avoids the chord through two distinct
finite rational points whose parameters lie outside that subfield. -/
theorem subfield_circle_nonzero (S : Subfield F) (t u x y : F)
    (h2 : (2 : F) ≠ 0) (ht : 1+t^2 ≠ 0) (hu : 1+u^2 ≠ 0)
    (htu : u ≠ t) (htS : t ∉ S) (huS : u ∉ S)
    (hxS : x ∈ S) (hyS : y ∈ S) (hc : x^2+y^2=1) :
    chord t u x y ≠ 0 := by
  have h4 : (4 : F) ≠ 0 := by
    have he : (4 : F) = 2*2 := by ring
    rw [he]
    exact mul_ne_zero h2 h2
  by_cases hx : 1+x=0
  · have hxe : x = -1 := by linear_combination hx
    have hy2 : y^2 = 0 := by
      rw [hxe] at hc
      linear_combination hc
    have hye : y = 0 := by
      have hh : y*y = 0 := by simpa only [pow_two] using hy2
      exact (mul_eq_zero.mp hh).elim id id
    rw [hxe, hye]
    exact exceptional_nonzero t u h4 ht hu htu
  · have hrS : y/(1+x) ∈ S := S.div_mem hyS (S.add_mem S.one_mem hxS)
    have hrt : y/(1+x) ≠ t := by
      intro h
      exact htS (h ▸ hrS)
    have hru : y/(1+x) ≠ u := by
      intro h
      exact huS (h ▸ hrS)
    have hr : 1+(y/(1+x))^2 ≠ 0 := by
      rw [recover_denom x y hx hc]
      exact div_ne_zero h2 hx
    have hp := recover_point x y h2 hx hc
    have hn := rational_nonzero t u (y/(1+x)) h4 ht hu hr htu hrt hru
    rw [hp.1, hp.2] at hn
    exact hn

#print axioms subfield_circle_nonzero
#print axioms recover_point
#print axioms rational_factor
#print axioms exceptional_factor
#print axioms rational_nonzero
#print axioms exceptional_nonzero
end AspisV8R15.CircleChord
