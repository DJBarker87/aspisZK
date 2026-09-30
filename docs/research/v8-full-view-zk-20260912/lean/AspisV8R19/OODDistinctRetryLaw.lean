import AspisV8R19.TwoSwapSourceDomains
import AspisV8R17.BoundedRejection

/-! Ideal outer distinct-retry law for secure OOD parameters.

The model fixes the first accepted value `u` and samples three independent
values from the exact nonzero-imaginary-part domain, accepting precisely those
different from `u`.  This file excludes inner QM31/OOD sampler failures and
does not identify this ideal law with a source-oracle execution. -/
set_option autoImplicit false
namespace AspisV8R19.OODDistinctRetryLaw
open AspisV8R15.ExactTowerBase
open AspisV8R15.ExactTowerChord
open AspisR19.TwoSwapSourceDomains
open AspisR19.TwoSwapFixedRootProbability
open AspisV8R17.BoundedRejection
open AspisV8Privacy
noncomputable section

local instance : DecidableEq QM31Exact := Classical.decEq _
local instance cm31Fintype : Fintype CM31Exact :=
  Fintype.ofEquiv (M31Exact × M31Exact)
    (QuadraticAlgebra.equivProd (-1 : M31Exact) 0).symm
local instance qm31Fintype : Fintype QM31Exact :=
  Fintype.ofEquiv (CM31Exact × CM31Exact)
    (QuadraticAlgebra.equivProd qm31R 0).symm

abbrev D := {z : QM31Exact // z.im ≠ 0}

local instance : DecidableEq D := Classical.decEq _
local instance : Nonempty D :=
  ⟨secureOODEquiv.symm
    ((0 : CM31Exact), ⟨(1 : CM31Exact), one_ne_zero⟩)⟩

def accept (u : D) (x : D) : Bool := decide (x ≠ u)

theorem domain_card : Fintype.card D = sourceMinimum := by
  have hnonzero : Fintype.card {z : CM31Exact // z ≠ 0} = P ^ 2 - 1 :=
    (Set.card_ne_eq (0 : CM31Exact)).trans
      (congrArg (fun n => n - 1) cm31_card)
  calc
    Fintype.card D = Fintype.card (CM31Exact × {z : CM31Exact // z ≠ 0}) :=
      Fintype.card_congr secureOODEquiv
    _ = Fintype.card CM31Exact * Fintype.card {z : CM31Exact // z ≠ 0} :=
      Fintype.card_prod _ _
    _ = P ^ 2 * Fintype.card {z : CM31Exact // z ≠ 0} :=
      congrArg (fun n => n * Fintype.card {z : CM31Exact // z ≠ 0}) cm31_card
    _ = P ^ 2 * (P ^ 2 - 1) := congrArg (fun n => P ^ 2 * n) hnonzero
    _ = sourceMinimum := rfl

theorem accepted_domain_card (u : D) :
    Fintype.card {x : D // accept u x = true} = sourceMinimum - 1 := by
  calc
    Fintype.card {x : D // accept u x = true} =
        Fintype.card {x : D // x ≠ u} := by
      apply Fintype.card_congr
      exact Equiv.subtypeEquivRight (by simp [accept])
    _ = Fintype.card D - 1 := Set.card_ne_eq u
    _ = sourceMinimum - 1 := congrArg (fun n => n - 1) domain_card

theorem failure_probability (u : D) :
    uniformProbability (@sample D (accept u) 3) none =
      1 / (sourceMinimum : ℚ) ^ 3 := by
  rw [AspisV8R17.BoundedRejection.failure_probability]
  have hfalse : Fintype.card {x : D // accept u x = false} = 1 := by
    simpa [accept] using (Fintype.card_subtype_eq u)
  rw [hfalse, domain_card]
  norm_num

theorem accepted_output_probabilities_equal (u v w : D)
    (hv : v ≠ u) (hw : w ≠ u) :
    uniformProbability (@sample D (accept u) 3) (some v) =
      uniformProbability (@sample D (accept u) 3) (some w) := by
  apply accepted_probabilities_equal (accept u) 3 v w
  · simpa only [accept, decide_eq_true_eq] using hv
  · simpa only [accept, decide_eq_true_eq] using hw

#print axioms domain_card
#print axioms accepted_domain_card
#print axioms failure_probability
#print axioms accepted_output_probabilities_equal
end
end AspisV8R19.OODDistinctRetryLaw
