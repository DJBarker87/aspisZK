import BoundedRetryKernel

/-! Rational unconditional mass adapter for the actual ordinary-sampler fibre
count. Abort remains in the denominator. The consumer must prove the displayed
cardinality identity for its literal decoder; uniformity is not inferred here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.FiniteOptionMass
noncomputable section
open Finset AspisV8.JointImageGame
variable {A V : Type*} [Fintype A] [Fintype V] [Nonempty A] [Nonempty V]

theorem avg_indicator_card (P : A → Prop) [DecidablePred P] :
    avg univ (fun a => if P a then 1 else 0) =
      (Fintype.card {a // P a} : ℚ) / Fintype.card A := by
  classical
  simp [avg, Fintype.card_subtype]

def successMass (draw : A → Option V) : ℚ :=
  avg univ (fun a => if (draw a).isSome then 1 else 0)

theorem unconditional_mass (draw : A → Option V) [DecidableEq V] (v : V)
    (fibres : Fintype.card {a // draw a = some v} * Fintype.card V =
      Fintype.card {a // (draw a).isSome}) :
    avg univ (fun a => if draw a = some v then 1 else 0) =
      successMass draw / Fintype.card V := by
  rw [avg_indicator_card, successMass, avg_indicator_card]
  have aNonzero : (Fintype.card A : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have vNonzero : (Fintype.card V : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have counts : (Fintype.card {a // draw a = some v} : ℚ) * Fintype.card V =
      Fintype.card {a // (draw a).isSome} := by exact_mod_cast fibres
  field_simp
  exact counts

#print axioms avg_indicator_card
#print axioms unconditional_mass
end
end AspisV8.FiniteOptionMass
