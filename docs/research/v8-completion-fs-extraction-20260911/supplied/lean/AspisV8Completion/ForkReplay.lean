/-
FIRST ATTEMPT — NOT COMPILED IN THE AUTHORING ENVIRONMENT.
No declaration in this file is a certification of Aspis or a source-refinement
claim unless its concrete producer and dependency chain are separately checked.
See docs/OBLIGATIONS.md and the per-module status manifest.
-/

import AspisV8Completion.CausalPrograms
import AspisV8Completion.ChronologicalPrefixes
set_option autoImplicit false
open scoped BigOperators
namespace AspisV8Completion.ForkReplay
open CausalPrograms
variable {Message Coin : Type*}

/-- Deterministic fork-prefix consistency, NOT a forking-success probability
or a source of magically authenticated extra openings. -/
theorem fork_prefix {n : Nat} (p : Program Message Coin n)
    (left right : Fin n → Coin) (cut : Nat)
    (same : ∀ i : Fin n, i.val < cut → left i = right i) :
    (execute p left).take cut = (execute p right).take cut :=
  execute_take_equal p left right cut same

/-- Explicit accounting for restarts. Repeated executed work counts even if
underlying oracle inputs were seen before; use a separate fresh-query count. -/
def replayCost (prefixSteps perSuffix replays : Nat) : Nat :=
  prefixSteps + replays*perSuffix

theorem replayCost_mono {prefix suffix n m : Nat} (le : n ≤ m) :
    replayCost prefix suffix n ≤ replayCost prefix suffix m := by
  unfold replayCost
  exact Nat.add_le_add_left (Nat.mul_le_mul_right suffix le) prefix

/-- A coherence group is explicitly all-pairs same-prefix. A mere count of
successful forks does not imply membership in such a group. -/
def Coherent {n : Nat} (p : Program Message Coin n)
    (forks : List (Fin n → Coin)) (cut : Nat) : Prop :=
  ∀ left ∈ forks, ∀ right ∈ forks,
    (execute p left).take cut = (execute p right).take cut

theorem coherent_of_common_coins {n : Nat} (p : Program Message Coin n)
    (forks : List (Fin n → Coin)) (reference : Fin n → Coin) (cut : Nat)
    (fixed : ∀ coins ∈ forks, ∀ i : Fin n, i.val < cut → coins i = reference i) :
    Coherent p forks cut := by
  intro left hl right hr
  apply fork_prefix p left right cut
  intro i hi
  exact (fixed left hl i hi).trans (fixed right hr i hi).symm

#print axioms coherent_of_common_coins
end AspisV8Completion.ForkReplay
