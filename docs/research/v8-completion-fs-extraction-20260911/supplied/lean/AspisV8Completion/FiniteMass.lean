/-
FIRST ATTEMPT — NOT COMPILED IN THE AUTHORING ENVIRONMENT.
No declaration in this file is a certification of Aspis or a source-refinement
claim unless its concrete producer and dependency chain are separately checked.
See docs/OBLIGATIONS.md and the per-module status manifest.
-/

import Mathlib
set_option autoImplicit false
open scoped BigOperators
namespace AspisV8Completion.FiniteMass
noncomputable section
variable {Ω : Type*} [Fintype Ω]

structure Distribution (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℚ
  nonneg : ∀ x, 0 ≤ weight x
  total : (∑ x, weight x) = 1

def mass (μ : Distribution Ω) (E : Ω → Prop) : ℚ := by
  classical
  exact ∑ x, if E x then μ.weight x else 0

theorem mass_nonneg (μ : Distribution Ω) (E : Ω → Prop) : 0 ≤ mass μ E := by
  classical
  unfold mass
  apply Finset.sum_nonneg
  intro x _
  split_ifs <;> simp_all [μ.nonneg]

theorem mass_mono (μ : Distribution Ω) (E F : Ω → Prop)
    (included : ∀ x, E x → F x) : mass μ E ≤ mass μ F := by
  classical
  unfold mass
  apply Finset.sum_le_sum
  intro x _
  by_cases he : E x
  · simp only [he, included x he, if_true]
    exact le_rfl
  · by_cases hf : F x
    · simp only [he, hf, if_false, if_true]
      exact μ.nonneg x
    · simp only [he, hf, if_false]
      exact le_rfl

theorem mass_true (μ : Distribution Ω) : mass μ (fun _ => True) = 1 := by
  classical
  simpa [mass] using μ.total

theorem mass_le_one (μ : Distribution Ω) (E : Ω → Prop) : mass μ E ≤ 1 := by
  simpa only [mass_true] using mass_mono μ E (fun _ => True) (fun _ _ => True.intro)

theorem mass_union (μ : Distribution Ω) (E F : Ω → Prop) :
    mass μ (fun x => E x ∨ F x) ≤ mass μ E + mass μ F := by
  classical
  unfold mass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases he : E x <;> by_cases hf : F x <;>
    simp [he, hf, μ.nonneg x]

theorem mass_disjoint_union (μ : Distribution Ω) (E F : Ω → Prop)
    (disjoint : ∀ x, ¬ (E x ∧ F x)) :
    mass μ (fun x => E x ∨ F x) = mass μ E + mass μ F := by
  classical
  unfold mass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases he : E x <;> by_cases hf : F x <;> simp_all

/-- Finite union bound. The source must separately supply the coverage inclusion. -/
theorem mass_exists_fin (μ : Distribution Ω) : ∀ n (E : Fin n → Ω → Prop),
    mass μ (fun x => ∃ i, E i x) ≤ ∑ i, mass μ (E i) := by
  classical
  intro n
  induction n with
  | zero =>
    intro E
    simp [mass]
  | succ n ih =>
    intro E
    have split : (fun x => ∃ i : Fin (n+1), E i x) =
        (fun x => E 0 x ∨ ∃ i : Fin n, E i.succ x) := by
      funext x
      apply propext
      constructor
      · rintro ⟨i, hi⟩
        refine Fin.cases ?_ (fun j hj => ?_) i hi
        · exact Or.inl
        · exact Or.inr ⟨j, hj⟩
      · rintro (h | ⟨i,h⟩)
        · exact ⟨0,h⟩
        · exact ⟨i.succ,h⟩
    rw [split, Fin.sum_univ_succ]
    exact (mass_union μ (E 0) (fun x => ∃ i : Fin n, E i.succ x)).trans
      (add_le_add_left (ih (fun i => E i.succ)) _)

/-- A law-preserving map transports an event; this is a conditional consumer,
not a proof that the actual FS experiment admits such a map. -/
theorem event_transport {Ξ : Type*} [Fintype Ξ]
    (μ : Distribution Ω) (ν : Distribution Ξ) (f : Ω → Ξ)
    (law : ∀ E, mass μ (fun x => E (f x)) = mass ν E)
    (bad : Ω → Prop) (idealBad : Ξ → Prop)
    (covered : ∀ x, bad x → idealBad (f x)) :
    mass μ bad ≤ mass ν idealBad := by
  rw [← law idealBad]
  exact mass_mono μ bad (fun x => idealBad (f x)) covered

#print axioms mass_union
#print axioms mass_exists_fin
#print axioms event_transport
end
end AspisV8Completion.FiniteMass
