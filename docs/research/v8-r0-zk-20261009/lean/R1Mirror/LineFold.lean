import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Exact field algebra for the four-value line fold.

These identities prove only the stated field recovery and Horner
recombination. They do not establish domain commutation, a bad-set bound, or
an encoder property. -/

set_option autoImplicit false

noncomputable section

namespace AspisR1

lemma four_ne_zero {K : Type*} [Field K] (h2ne : (2 : K) ≠ 0) :
    (4 : K) ≠ 0 := by
  have h4 : (4 : K) = (2 : K) * 2 := by ring
  rw [h4]
  exact mul_ne_zero h2ne h2ne

variable {K : Type*} [Field K]
variable (h0 h1 h2 h3 x y z : K)

def a (h0 h1 h2 h3 x y z : K) : K :=
  h0 + x * h1 + z * h2 + x * z * h3
def b (h0 h1 h2 h3 x y z : K) : K :=
  h0 - x * h1 + z * h2 - x * z * h3
def c (h0 h1 h2 h3 x y z : K) : K :=
  h0 - y * h1 - z * h2 + y * z * h3
def d (h0 h1 h2 h3 x y z : K) : K :=
  h0 + y * h1 - z * h2 - y * z * h3

def C0 : K := (a h0 h1 h2 h3 x y z - b h0 h1 h2 h3 x y z) / (2 * x)
def C1 : K := (d h0 h1 h2 h3 x y z - c h0 h1 h2 h3 x y z) / (2 * y)

theorem recover_h0 :
    (2 : K) ≠ 0 → h0 = (a h0 h1 h2 h3 x y z + b h0 h1 h2 h3 x y z +
      c h0 h1 h2 h3 x y z + d h0 h1 h2 h3 x y z) / 4 := by
  intro hh
  dsimp [a, b, c, d]
  field_simp [four_ne_zero hh]
  <;> ring

theorem recover_h2 :
    z ≠ 0 → (2 : K) ≠ 0 → h2 = (a h0 h1 h2 h3 x y z + b h0 h1 h2 h3 x y z -
      c h0 h1 h2 h3 x y z - d h0 h1 h2 h3 x y z) / (4 * z) := by
  intro hzz hh
  dsimp [a, b, c, d]
  field_simp [four_ne_zero hh, hzz]
  <;> ring

theorem recover_C0 :
    x ≠ 0 → (2 : K) ≠ 0 → C0 h0 h1 h2 h3 x y z = h1 + z * h3 := by
  intro hxx hh
  dsimp [C0, a, b]
  field_simp [hh, hxx]
  <;> ring

theorem recover_C1 :
    y ≠ 0 → (2 : K) ≠ 0 → C1 h0 h1 h2 h3 x y z = h1 - z * h3 := by
  intro hyy hh
  dsimp [C1, c, d]
  field_simp [hh, hyy]
  <;> ring

theorem recover_h1 :
    x ≠ 0 → y ≠ 0 → (2 : K) ≠ 0 → h1 =
      (C0 h0 h1 h2 h3 x y z + C1 h0 h1 h2 h3 x y z) / 2 := by
  intro hxx hyy hh
  rw [recover_C0 h0 h1 h2 h3 x y z hxx hh,
    recover_C1 h0 h1 h2 h3 x y z hyy hh]
  field_simp [hh]
  <;> ring

theorem recover_h3 :
    x ≠ 0 → y ≠ 0 → z ≠ 0 → (2 : K) ≠ 0 → h3 =
      (C0 h0 h1 h2 h3 x y z - C1 h0 h1 h2 h3 x y z) / (2 * z) := by
  intro hxx hyy hzz hh
  rw [recover_C0 h0 h1 h2 h3 x y z hxx hh,
    recover_C1 h0 h1 h2 h3 x y z hyy hh]
  field_simp [hh, hzz]
  <;> ring

theorem recovered_horner (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (h2ne : (2 : K) ≠ 0) (alpha : K) :
    (a h0 h1 h2 h3 x y z + b h0 h1 h2 h3 x y z +
        c h0 h1 h2 h3 x y z + d h0 h1 h2 h3 x y z) / 4 +
      alpha * ((C0 h0 h1 h2 h3 x y z + C1 h0 h1 h2 h3 x y z) / 2 +
        alpha * ((a h0 h1 h2 h3 x y z + b h0 h1 h2 h3 x y z -
            c h0 h1 h2 h3 x y z - d h0 h1 h2 h3 x y z) / (4 * z) +
          alpha * ((C0 h0 h1 h2 h3 x y z - C1 h0 h1 h2 h3 x y z) / (2 * z)))) =
      h0 + alpha * (h1 + alpha * (h2 + alpha * h3)) := by
  rw [← recover_h0 h0 h1 h2 h3 x y z h2ne,
    ← recover_h1 h0 h1 h2 h3 x y z hx hy h2ne,
    ← recover_h2 h0 h1 h2 h3 x y z hz h2ne,
    ← recover_h3 h0 h1 h2 h3 x y z hx hy hz h2ne]

#print axioms recover_h0
#print axioms recover_h2
#print axioms recover_C0
#print axioms recover_C1
#print axioms recover_h1
#print axioms recover_h3
#print axioms recovered_horner

end AspisR1

end
