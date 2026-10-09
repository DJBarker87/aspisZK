/-
FIRST ATTEMPT — NOT COMPILED IN THE AUTHORING ENVIRONMENT.
No declaration in this file is a certification of Aspis or a source-refinement
claim unless its concrete producer and dependency chain are separately checked.
See docs/OBLIGATIONS.md and the per-module status manifest.
-/

import AspisV8Completion.FiniteMass
import AspisV8Completion.AdaptiveHazard
set_option autoImplicit false
open scoped BigOperators
namespace AspisV8Completion.FiatShamirTransport
open FiniteMass
noncomputable section
variable {Real Ideal : Type*} [Fintype Real] [Fintype Ideal]

/-- Conditional game-hop CONSUMER. The real/source coupling and uniform
strategy producer are not hidden inside a definition of successful execution.
This theorem alone does not close any Aspis FS obligation. -/
theorem lift_with_exception
    (real : Distribution Real) (ideal : Distribution Ideal) (map : Real → Ideal)
    (realBad exception : Real → Prop) (idealBad : Ideal → Prop)
    (coupled : ∀ event, mass real (fun r => event (map r)) = mass ideal event)
    (sourceCover : ∀ r, realBad r → exception r ∨ idealBad (map r))
    (exceptionBound idealBound : ℚ)
    (exceptionSmall : mass real exception ≤ exceptionBound)
    (idealSmall : mass ideal idealBad ≤ idealBound) :
    mass real realBad ≤ exceptionBound+idealBound := by
  have covered := mass_mono real realBad
    (fun r => exception r ∨ idealBad (map r)) sourceCover
  have union := mass_union real exception (fun r => idealBad (map r))
  rw [coupled idealBad] at union
  exact covered.trans (union.trans (add_le_add exceptionSmall idealSmall))

/-- Multiple adaptive attempts are not free. This uniform-kernel theorem
allows arbitrary dependence on earlier states, but demands an actual local
hazard proof at every reachable source state. -/
theorem bounded_adaptive_attempts {S A : Type*} [Fintype A]
    (kernel : AdaptiveHazard.Kernel S A) (ε : ℚ) (nonneg : 0 ≤ ε)
    (localProof : ∀ state, AdaptiveHazard.localMass kernel state ≤ ε)
    (attempts : Nat) (initial : S) :
    AdaptiveHazard.ever kernel attempts initial ≤ (attempts:ℚ)*ε :=
  AdaptiveHazard.ever_le_budget kernel ε nonneg localProof attempts initial

/-- If an actual uniform map cannot be produced, leave lift_with_exception
uninstantiated. A pointwise existential ideal execution is NOT its coupled
premise and must not be substituted. See docs/FIAT_SHAMIR.md. -/
#print axioms lift_with_exception
#print axioms bounded_adaptive_attempts
end
end AspisV8Completion.FiatShamirTransport
