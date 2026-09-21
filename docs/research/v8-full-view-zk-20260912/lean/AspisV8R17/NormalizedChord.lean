import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Rational circle chord normalization. Algebra only: no sampler law. -/
set_option autoImplicit false
namespace AspisV8R17
variable {F : Type*} [Field F]

def rationalX (u : F) : F := (1-u^2)/(1+u^2)
def rationalY (u : F) : F := 2*u/(1+u^2)
def chordScale (u v : F) : F := 2*(v-u)/((1+u^2)*(1+v^2))

theorem rational_chord_normalization (u v : F)
    (hu : 1+u^2 ≠ 0) (hv : 1+v^2 ≠ 0) :
    rationalX u * rationalY v - rationalY u * rationalX v =
      chordScale u v * (1+u*v) ∧
    rationalY u - rationalY v = chordScale u v * (u*v-1) ∧
    rationalX v - rationalX u = chordScale u v * (-(u+v)) := by
  unfold rationalX rationalY chordScale
  constructor
  · field_simp
    <;> ring
  constructor
  · field_simp
    <;> ring
  · field_simp
    <;> ring

theorem chordScale_ne_zero (u v : F) (h2 : (2:F) ≠ 0)
    (hu : 1+u^2 ≠ 0) (hv : 1+v^2 ≠ 0) (hne : v ≠ u) :
    chordScale u v ≠ 0 := by
  exact div_ne_zero (mul_ne_zero h2 (sub_ne_zero.mpr hne)) (mul_ne_zero hu hv)

#print axioms rational_chord_normalization
#print axioms chordScale_ne_zero
end AspisV8R17
