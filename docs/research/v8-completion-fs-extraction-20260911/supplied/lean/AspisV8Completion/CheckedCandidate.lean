/-
FIRST ATTEMPT — NOT COMPILED IN THE AUTHORING ENVIRONMENT.
No declaration in this file is a certification of Aspis or a source-refinement
claim unless its concrete producer and dependency chain are separately checked.
See docs/OBLIGATIONS.md and the per-module status manifest.
-/

import Mathlib
set_option autoImplicit false
open scoped BigOperators
namespace AspisV8Completion.CheckedCandidate
variable {W : Type*}

/-- Executable bounded search over an already supplied finite candidate list.
It does NOT prove that candidates are obtainable from allowed ROM access. -/
def search (check : W → Bool) : Nat → List W → Option W
  | 0, _ => none
  | _, [] => none
  | n+1, w::rest => if check w then some w else search check n rest

theorem result_checked (check : W → Bool) : ∀ n candidates w,
    search check n candidates = some w → check w = true := by
  intro n
  induction n with
  | zero => intro candidates w h; simp [search] at h
  | succ n ih =>
    intro candidates w h
    cases candidates with
    | nil => simp [search] at h
    | cons head rest =>
      simp only [search] at h
      split at h
      · rename_i passes
        have same : head = w := Option.some.inj h
        exact same ▸ passes
      · exact ih rest w h

theorem result_member (check : W → Bool) : ∀ n candidates w,
    search check n candidates = some w → w ∈ candidates := by
  intro n
  induction n with
  | zero => intro candidates w h; simp [search] at h
  | succ n ih =>
    intro candidates w h
    cases candidates with
    | nil => simp [search] at h
    | cons head rest =>
      simp only [search] at h
      split at h
      · have same : head = w := Option.some.inj h
        simp [same]
      · exact List.mem_cons_of_mem _ (ih rest w h)

/-- Completeness for a FULLY AVAILABLE bounded candidate list. This is not
an assumption that a decoded algebraic witness validates as a payment. -/
theorem finds_some (check : W → Bool) : ∀ candidates n,
    candidates.length ≤ n → (∃ w ∈ candidates, check w=true) →
    ∃ w, search check n candidates = some w := by
  intro candidates
  induction candidates with
  | nil => intro n enough h; simp at h
  | cons head rest ih =>
    intro n enough h
    cases n with
    | zero => simp at enough
    | succ n =>
      by_cases passes : check head = true
      · exact ⟨head, by simp [search, passes]⟩
      · obtain ⟨w,member,good⟩ := h
        have inRest : w ∈ rest := by
          rcases List.mem_cons.mp member with eq | member
          · subst w; contradiction
          · exact member
        obtain ⟨out,found⟩ := ih n (by simpa using enough) ⟨w,inRest,good⟩
        exact ⟨out, by simpa [search, passes] using found⟩

#print axioms result_checked
#print axioms finds_some
end AspisV8Completion.CheckedCandidate
