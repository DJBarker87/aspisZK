import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum

/-!
# A fresh holdout after adaptive tuple reconstruction

The selected object may depend arbitrarily on the complete earlier history.
The challenge below is a NEW coordinate, not one of the coordinates used to
select that object.  A validation implication and a pointwise exceptional-set
bound give a direct finite history-by-challenge count.  No uniform law for an
actual Fiat--Shamir execution, successful collector, or source correspondence
is asserted.  In particular this theorem cannot charge the original 29 nodes
against the tuple reconstructed from those same nodes.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 150000

namespace AspisV8.PostselectedGammaHoldout
open Finset
noncomputable section
variable {History Gamma Candidate : Type*}
local instance decision (p : Prop) : Decidable p := Classical.propDecidable p

/-- Literal validation pairs in the new product experiment. -/
def validationPairs (histories : Finset History) (domain : Finset Gamma)
    (validate : History → Gamma → Prop) : Finset (History × Gamma) := by
  classical
  exact histories.biUnion fun h => {h} ×ˢ domain.filter (validate h)

theorem mem_validationPairs (histories : Finset History) (domain : Finset Gamma)
    (validate : History → Gamma → Prop) (h : History) (g : Gamma) :
    (h, g) ∈ validationPairs histories domain validate ↔
      h ∈ histories ∧ g ∈ domain ∧ validate h g := by
  classical
  simp [validationPairs, and_assoc]

/-- The selected candidate is allowed to depend on h; no bound on its range is
needed.  Soundness of the additional validation is an explicit premise. -/
theorem conditional_card_le (domain : Finset Gamma)
    (select : History → Candidate) (bad : Candidate → Finset Gamma)
    (validate : History → Gamma → Prop) (h : History) (cap : Nat)
    (bounded : (bad (select h)).card ≤ cap)
    (sound : ∀ g ∈ domain, validate h g → g ∈ bad (select h)) :
    (domain.filter (validate h)).card ≤ cap := by
  classical
  have subset : domain.filter (validate h) ⊆ bad (select h) := by
    intro g member
    exact sound g (Finset.mem_filter.mp member).1 (Finset.mem_filter.mp member).2
  exact (Finset.card_le_card subset).trans bounded

/-- Direct finite sum/count across history-by-fresh-challenge witnesses. -/
theorem validation_card_le (histories : Finset History) (domain : Finset Gamma)
    (select : History → Candidate) (bad : Candidate → Finset Gamma)
    (validate : History → Gamma → Prop) (cap : Nat)
    (bounded : ∀ h ∈ histories, (bad (select h)).card ≤ cap)
    (sound : ∀ h ∈ histories, ∀ g ∈ domain,
      validate h g → g ∈ bad (select h)) :
    (validationPairs histories domain validate).card ≤ histories.card * cap := by
  classical
  unfold validationPairs
  apply Finset.card_biUnion_le_card_mul
  intro h member
  simpa only [Finset.card_product, Finset.card_singleton, one_mul] using
    conditional_card_le domain select bad validate h cap
      (bounded h member) (sound h member)

/-- Uniform finite product law only.  For nonuniform earlier histories, the
pointwise conditional_card_le bound can instead be averaged under that law. -/
theorem validation_mass_le (histories : Finset History) (domain : Finset Gamma)
    (select : History → Candidate) (bad : Candidate → Finset Gamma)
    (validate : History → Gamma → Prop) (cap : Nat)
    (historiesNonempty : histories.Nonempty) (domainNonempty : domain.Nonempty)
    (bounded : ∀ h ∈ histories, (bad (select h)).card ≤ cap)
    (sound : ∀ h ∈ histories, ∀ g ∈ domain,
      validate h g → g ∈ bad (select h)) :
    ((validationPairs histories domain validate).card : ℚ) /
        ((histories.card : ℚ) * (domain.card : ℚ)) ≤
      (cap : ℚ) / (domain.card : ℚ) := by
  have positiveH : (0 : ℚ) < histories.card := by
    exact_mod_cast historiesNonempty.card_pos
  have positiveG : (0 : ℚ) < domain.card := by
    exact_mod_cast domainNonempty.card_pos
  have countBound : ((validationPairs histories domain validate).card : ℚ) ≤
      (histories.card : ℚ) * (cap : ℚ) := by
    exact_mod_cast validation_card_le histories domain select bad validate cap bounded sound
  calc
    ((validationPairs histories domain validate).card : ℚ) /
        ((histories.card : ℚ) * (domain.card : ℚ)) ≤
        ((histories.card : ℚ) * (cap : ℚ)) /
          ((histories.card : ℚ) * (domain.card : ℚ)) :=
      div_le_div_of_nonneg_right countBound (le_of_lt (mul_pos positiveH positiveG))
    _ = (cap : ℚ) / (domain.card : ℚ) :=
      mul_div_mul_left _ _ (ne_of_gt positiveH)

end
end AspisV8.PostselectedGammaHoldout

#print axioms AspisV8.PostselectedGammaHoldout.mem_validationPairs
#print axioms AspisV8.PostselectedGammaHoldout.conditional_card_le
#print axioms AspisV8.PostselectedGammaHoldout.validation_card_le
#print axioms AspisV8.PostselectedGammaHoldout.validation_mass_le
