/-
FIRST ATTEMPT — NOT COMPILED IN THE AUTHORING ENVIRONMENT.
No declaration in this file is a certification of Aspis or a source-refinement
claim unless its concrete producer and dependency chain are separately checked.
See docs/OBLIGATIONS.md and the per-module status manifest.
-/

import AspisV8Completion.UniformStep
import AspisV8Completion.OracleCache
set_option autoImplicit false
open scoped BigOperators
namespace AspisV8Completion.LazyROHazard
noncomputable section
variable {S I A : Type*} [DecidableEq I] [Fintype A] [Nonempty A]

structure MachineState (S I A : Type*) where
  user : S
  oracle : OracleCache.State I A

/-- Adversary instructions see ONLY the current state/cache. A fresh random
answer is drawn afterwards. No completed transcript parameter is supplied. -/
structure Machine (S I A : Type*) where
  request : MachineState S I A → I
  advance : MachineState S I A → A → S
  freshBad : MachineState S I A → A → Bool

def kernel (m : Machine S I A) : AdaptiveHazard.Kernel (MachineState S I A) A where
  weight := fun _ a => UniformStep.weight a
  nonneg := fun _ a => UniformStep.weight_nonneg a
  total := fun _ => UniformStep.weight_total
  next := fun s coin =>
    let result := OracleCache.query s.oracle (m.request s) coin
    ⟨m.advance s result.1, result.2⟩
  hit := fun s coin =>
    match s.oracle.cache (m.request s) with
    | some _ => false
    | none => m.freshBad s coin

/-- The selected bad event is a fresh-exposure hazard only. A future-chosen
bad target attached to an old cached answer does NOT satisfy source coverage. -/
theorem local_bound (m : Machine S I A) (maxTargets : Nat)
    (small : ∀ s, (UniformStep.badSet (m.freshBad s)).card ≤ maxTargets) :
    ∀ s, AdaptiveHazard.localMass (kernel m) s ≤ maxTargets/(Fintype.card A : ℚ) := by
  intro s
  unfold AdaptiveHazard.localMass kernel
  cases h : s.oracle.cache (m.request s) with
  | none =>
    simp only [h]
    exact UniformStep.hit_mass_bound (m.freshBad s) maxTargets (small s)
  | some answer =>
    simp only [h, Bool.false_eq_true, ↓reduceIte, mul_zero, Finset.sum_const_zero]
    positivity

/-- Complete finite reference-machine hazard bound. Still requires actual
Rust/FS-to-reference-machine refinement and coverage of the intended event. -/
theorem fresh_hazard_bound (m : Machine S I A) (maxTargets : Nat)
    (small : ∀ s, (UniformStep.badSet (m.freshBad s)).card ≤ maxTargets)
    (calls : Nat) (initial : MachineState S I A) :
    AdaptiveHazard.ever (kernel m) calls initial ≤
      (calls:ℚ)*(maxTargets/(Fintype.card A : ℚ)) := by
  exact AdaptiveHazard.ever_le_budget (kernel m) _ (by positivity)
    (local_bound m maxTargets small) calls initial

#print axioms fresh_hazard_bound
end
end AspisV8Completion.LazyROHazard
