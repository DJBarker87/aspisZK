import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Explicit two-point interpolation using only 1, x, y. No random-rank
assumption or circle-coordinate exclusion beyond distinct points. The
legal-pad-to-basis correspondence is a separate source bridge. -/
set_option autoImplicit false
namespace AspisV8R17
variable {F : Type*} [Field F]

theorem affine_two_values (t0 t1 v0 v1 : F) (hne : t1 ≠ t0) :
    let b := (v1-v0)/(t1-t0)
    (v0-b*t0)+b*t0 = v0 ∧ (v0-b*t0)+b*t1 = v1 := by
  dsimp
  constructor
  · ring
  · have hd : t1-t0 ≠ 0 := sub_ne_zero.mpr hne
    field_simp
    <;> ring

theorem distinct_point_affine_surjective (p0 p1 : F × F)
    (hne : p1 ≠ p0) (v0 v1 : F) :
    ∃ a b c : F,
      a + b*p0.1 + c*p0.2 = v0 ∧
      a + b*p1.1 + c*p1.2 = v1 := by
  by_cases hy : p1.2 ≠ p0.2
  · obtain ⟨h0,h1⟩ := affine_two_values p0.2 p1.2 v0 v1 hy
    refine ⟨v0-((v1-v0)/(p1.2-p0.2))*p0.2, 0,
      (v1-v0)/(p1.2-p0.2), ?_, ?_⟩
    · simpa using h0
    · simpa using h1
  · have hx : p1.1 ≠ p0.1 := by
      intro hx
      exact hne (Prod.ext hx (not_ne_iff.mp hy))
    obtain ⟨h0,h1⟩ := affine_two_values p0.1 p1.1 v0 v1 hx
    refine ⟨v0-((v1-v0)/(p1.1-p0.1))*p0.1,
      (v1-v0)/(p1.1-p0.1), 0, ?_, ?_⟩
    · simpa using h0
    · simpa using h1

#print axioms affine_two_values
#print axioms distinct_point_affine_surjective
end AspisV8R17
