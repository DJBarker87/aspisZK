/-
FIRST ATTEMPT — NOT COMPILED IN THE AUTHORING ENVIRONMENT.
No declaration in this file is a certification of Aspis or a source-refinement
claim unless its concrete producer and dependency chain are separately checked.
See docs/OBLIGATIONS.md and the per-module status manifest.
-/

import AspisV8Completion.FiniteMass
set_option autoImplicit false
open scoped BigOperators
namespace AspisV8Completion.GlobalLedger
open FiniteMass
noncomputable section
variable {Run : Type*} [Fintype Run]

/-- Eight named classes are supplied by the intended source security game.
The coverage theorem is an explicit producer obligation, not a definition
of BadPayment. This generic consumer cannot be advertised as global closure. -/
theorem compose_eight (μ : Distribution Run) (bad : Run → Prop)
    (events : Fin 8 → Run → Prop) (bounds : Fin 8 → ℚ)
    (cover : ∀ run, bad run → ∃ i, events i run)
    (small : ∀ i, mass μ (events i) ≤ bounds i) :
    mass μ bad ≤ ∑ i, bounds i := by
  have inclusion := mass_mono μ bad (fun run => ∃ i, events i run) cover
  have union := mass_exists_fin μ 8 events
  exact inclusion.trans (union.trans (Finset.sum_le_sum (fun i _ => small i)))

/-- Threshold test in rationals; no rounded display bits are used. -/
theorem threshold (probability : ℚ) (terms : Fin 8 → ℚ)
    (ledger : probability ≤ ∑ i, terms i)
    (exactArithmetic : (∑ i, terms i) ≤ 1/(2:ℚ)^100) :
    probability ≤ 1/(2:ℚ)^100 := ledger.trans exactArithmetic

#print axioms compose_eight
#print axioms threshold
end
end AspisV8Completion.GlobalLedger
