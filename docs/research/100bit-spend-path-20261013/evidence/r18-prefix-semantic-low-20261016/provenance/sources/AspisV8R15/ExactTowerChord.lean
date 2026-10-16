import AspisV8R15.CircleChord
import AspisV8R15.ExactTowerBase

/-! Exact-tower algebraic instantiation, not an executable Rust refinement. -/
set_option autoImplicit false
namespace AspisV8R15.ExactTowerChord
open AspisV8R15.ExactTowerBase
open AspisV8R15.CircleChord

def cm31Subfield : Subfield QM31Exact :=
  (algebraMap CM31Exact QM31Exact).fieldRange

theorem mem_cm31_iff (z : QM31Exact) : z ∈ cm31Subfield ↔ z.im = 0 := by
  change (∃ a : CM31Exact, algebraMap CM31Exact QM31Exact a = z) ↔ _
  constructor
  · rintro ⟨a, rfl⟩
    rfl
  · intro h
    refine ⟨z.re, ?_⟩
    ext <;> simp [QuadraticAlgebra.algebraMap_eq, h]

theorem two_ne_zero : (2 : QM31Exact) ≠ 0 := by
  intro h
  have hh := congrArg (fun z : QM31Exact => z.re.re) h
  change (2 : M31Exact) = 0 at hh
  have hn : (2 : M31Exact) ≠ 0 := by
    change ¬ ((2 : ℕ) : ZMod P) = 0
    rw [ZMod.natCast_eq_zero_iff]
    decide
  exact hn hh

/-- The source's rejected `c1 == 0` parameters correspond exactly to the
CM31 subfield. No caller-supplied abstract field or subfield remains here. -/
theorem chord_nonzero (t u : QM31Exact) (x y : CM31Exact)
    (ht : 1+t^2 ≠ 0) (hu : 1+u^2 ≠ 0)
    (htu : u ≠ t) (htim : t.im ≠ 0) (huim : u.im ≠ 0)
    (hc : x^2+y^2=1) :
    chord t u (algebraMap CM31Exact QM31Exact x)
      (algebraMap CM31Exact QM31Exact y) ≠ 0 := by
  apply subfield_circle_nonzero cm31Subfield t u _ _ two_ne_zero ht hu htu
  · exact fun h => htim ((mem_cm31_iff t).mp h)
  · exact fun h => huim ((mem_cm31_iff u).mp h)
  · exact (algebraMap CM31Exact QM31Exact).mem_fieldRange_self x
  · exact (algebraMap CM31Exact QM31Exact).mem_fieldRange_self y
  · have h := congrArg (algebraMap CM31Exact QM31Exact) hc
    simpa only [map_add, map_pow, map_one] using h

theorem source_policy_chord_nonzero (t u : QM31Exact) (x y : CM31Exact)
    (ht : 1+t^2 ≠ 0) (hu : 1+u^2 ≠ 0)
    (hpoints : (px t, py t) ≠ (px u, py u))
    (htim : t.im ≠ 0) (huim : u.im ≠ 0) (hc : x^2+y^2=1) :
    chord t u (algebraMap CM31Exact QM31Exact x)
      (algebraMap CM31Exact QM31Exact y) ≠ 0 := by
  apply chord_nonzero t u x y ht hu _ htim huim hc
  intro h
  apply hpoints
  rw [h]

#print axioms source_policy_chord_nonzero
#print axioms mem_cm31_iff
#print axioms two_ne_zero
#print axioms chord_nonzero
end AspisV8R15.ExactTowerChord
