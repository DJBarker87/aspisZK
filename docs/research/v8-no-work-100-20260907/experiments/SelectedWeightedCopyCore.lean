import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Narrow port of the generic row algebra in
NativePaymentCompiledCopyLogUpV1, with the selected source's factored
residual and five public weight kinds. No imported 78/75/183-link registry,
semantic acceptance premise, witness, or probabilistic claim is used.

The full Native leaf's uncached endpoint closure is deliberately not rebuilt.
The selected 136-link table-to-row/source refinement and the later
tagged-multiset implication are separate from this weighted-row theorem.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 150000

namespace AspisV8.SelectedWeightedCopyCore
open scoped BigOperators

inductive Variant where
  | transfer
  | withdrawal
  deriving DecidableEq

/-- The actual five `link_weight` cases. `level` records the public
generated weight level; no witness direction is used here. -/
inductive WeightKind where
  | one
  | transfer
  | withdrawal
  | appendLeft (level : Nat)
  | appendRight (level : Nat)

def weightBit (variant : Variant) (appendIndex : Nat) : WeightKind → Bool
  | .one => true
  | .transfer => decide (variant = .transfer)
  | .withdrawal => decide (variant = .withdrawal)
  | .appendLeft level => !(appendIndex.testBit level)
  | .appendRight level => appendIndex.testBit level

def publicWeight {K : Type*} [Zero K] [One K]
    (variant : Variant) (appendIndex : Nat) (kind : WeightKind) : K :=
  if weightBit variant appendIndex kind then 1 else 0

theorem publicWeight_binary {K : Type*} [Zero K] [One K]
    (variant : Variant) (appendIndex : Nat) (kind : WeightKind) :
    publicWeight (K := K) variant appendIndex kind = 0 ∨
      publicWeight (K := K) variant appendIndex kind = 1 := by
  unfold publicWeight
  split <;> simp

theorem append_weights_sum {K : Type*} [AddZeroClass K] [One K]
    (variant : Variant) (appendIndex level : Nat) :
    publicWeight (K := K) variant appendIndex (.appendLeft level) +
      publicWeight (K := K) variant appendIndex (.appendRight level) = 1 := by
  cases h : appendIndex.testBit level <;> simp [publicWeight, weightBit, h]

structure Row (K : Type*) where
  producerValue : Fin 2 → K
  producerWeight : Fin 2 → K
  consumerValue : Fin 2 → K
  consumerWeight : Fin 2 → K

variable {K : Type*} [Field K]

/-- Literal field expression in the selected `copy_residual`, including
the denominators of both slots regardless of their public weight. -/
def sourceResidual (row : Row K) (helper chi : K) : K :=
  let p0 := chi - row.producerValue 0
  let p1 := chi - row.producerValue 1
  let c0 := chi - row.consumerValue 0
  let c1 := chi - row.consumerValue 1
  let pd := p0 * p1
  let cd := c0 * c1
  let pn := row.producerWeight 0 * p1 + row.producerWeight 1 * p0
  let cn := row.consumerWeight 0 * c1 + row.consumerWeight 1 * c0
  pd * (helper * cd + cn) - cd * pn

/-- The expression already used by the older generic Native row lemma. -/
def expandedResidual (row : Row K) (helper chi : K) : K :=
  let p0 := chi - row.producerValue 0
  let p1 := chi - row.producerValue 1
  let c0 := chi - row.consumerValue 0
  let c1 := chi - row.consumerValue 1
  helper * p0 * p1 * c0 * c1
    - row.producerWeight 0 * p1 * c0 * c1
    - row.producerWeight 1 * p0 * c0 * c1
    + row.consumerWeight 0 * p0 * p1 * c1
    + row.consumerWeight 1 * p0 * p1 * c0

theorem sourceResidual_eq_expanded (row : Row K) (helper chi : K) :
    sourceResidual row helper chi = expandedResidual row helper chi := by
  dsimp [sourceResidual, expandedResidual]
  ring

def rationalContribution (row : Row K) (chi : K) : K :=
  (∑ slot : Fin 2, row.producerWeight slot * (chi - row.producerValue slot)⁻¹) -
    ∑ slot : Fin 2, row.consumerWeight slot * (chi - row.consumerValue slot)⁻¹

/-- Deliberately includes zero-weight slots, not merely the active-link
poles in the eventual global rational expression. -/
def NoSlotPole (row : Row K) (chi : K) : Prop :=
  (∀ slot, chi - row.producerValue slot ≠ 0) ∧
    ∀ slot, chi - row.consumerValue slot ≠ 0

/-- Port of NativePaymentCompiledCopyLogUpV1's generic field proof. -/
theorem helper_eq_rational_of_source_zero
    (row : Row K) (helper chi : K)
    (noPole : NoSlotPole row chi)
    (zero : sourceResidual row helper chi = 0) :
    helper = rationalContribution row chi := by
  have residual : expandedResidual row helper chi = 0 := by
    rw [← sourceResidual_eq_expanded]
    exact zero
  unfold rationalContribution
  simp only [Fin.sum_univ_two]
  field_simp [noPole.1 0, noPole.1 1, noPole.2 0, noPole.2 1]
  unfold expandedResidual at residual
  dsimp only at residual
  linear_combination residual

theorem rationalContribution_zero_weights (row : Row K) (chi : K)
    (producerZero : ∀ slot, row.producerWeight slot = 0)
    (consumerZero : ∀ slot, row.consumerWeight slot = 0) :
    rationalContribution row chi = 0 := by
  simp only [rationalContribution, producerZero, consumerZero,
    zero_mul, Finset.sum_const_zero, sub_zero]

/-- A permanent source-expression regression: a zero-weight slot's pole
can hide a nonzero helper in the cross-multiplied row check. -/
def zeroWeightPoleRow (chi : K) : Row K where
  producerValue := fun _ => chi
  producerWeight := fun _ => 0
  consumerValue := fun _ => 0
  consumerWeight := fun _ => 0

theorem zero_weight_pole_regression (chi : K) :
    sourceResidual (zeroWeightPoleRow chi) 1 chi = 0 ∧
      rationalContribution (zeroWeightPoleRow chi) chi = 0 ∧
      (1 : K) ≠ rationalContribution (zeroWeightPoleRow chi) chi := by
  have rat : rationalContribution (zeroWeightPoleRow chi) chi = 0 :=
    rationalContribution_zero_weights _ _ (fun _ => rfl) (fun _ => rfl)
  refine ⟨?_, rat, ?_⟩
  · simp [sourceResidual, zeroWeightPoleRow]
  · rw [rat]
    exact one_ne_zero

section Global
variable {I : Type*} [Fintype I] (active : I → Prop) [DecidablePred active]

def gatedResidual (rows : I → Row K) (helper : I → K) (chi : K) (i : I) : K :=
  if active i then sourceResidual (rows i) (helper i) chi else 0

def inactiveHelper (helper : I → K) (i : I) : K :=
  if active i then 0 else helper i

def activeBalance (rows : I → Row K) (chi : K) : K :=
  ∑ i, if active i then rationalContribution (rows i) chi else 0

/-- Whole-table deterministic bridge. The total and inactive helper sums
are independent checked-boundary obligations; neither is inferred from a
zero random aggregate. No coefficient table or received oracle is assumed
to be a valid payment or an exact codeword. -/
theorem active_balance_zero_of_rows
    (rows : I → Row K) (helper : I → K) (chi : K)
    (localZero : ∀ i, gatedResidual active rows helper chi i = 0)
    (totalZero : (∑ i, helper i) = 0)
    (inactiveZero : (∑ i, inactiveHelper active helper i) = 0)
    (noPole : ∀ i, active i → NoSlotPole (rows i) chi) :
    activeBalance active rows chi = 0 := by
  have pointwise : ∀ i,
      (if active i then rationalContribution (rows i) chi else 0) +
        inactiveHelper active helper i = helper i := by
    intro i
    by_cases ai : active i
    · have rz : sourceResidual (rows i) (helper i) chi = 0 := by
        simpa only [gatedResidual, if_pos ai] using localZero i
      have exactHelper := helper_eq_rational_of_source_zero
        (rows i) (helper i) chi (noPole i ai) rz
      simp only [if_pos ai, inactiveHelper, add_zero]
      exact exactHelper.symm
    · simp only [if_neg ai, inactiveHelper, zero_add]
  have summed : activeBalance active rows chi +
      (∑ i, inactiveHelper active helper i) = ∑ i, helper i := by
    rw [activeBalance, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => pointwise i)
  rw [inactiveZero, totalZero, add_zero] at summed
  exact summed

/-- Static inactive-weight coverage suffices to replace the gated sum by
the whole row sum. It does not remove any zero-weight denominator premise
from the preceding local-to-helper step. -/
theorem whole_balance_zero_of_rows
    (rows : I → Row K) (helper : I → K) (chi : K)
    (localZero : ∀ i, gatedResidual active rows helper chi i = 0)
    (totalZero : (∑ i, helper i) = 0)
    (inactiveZero : (∑ i, inactiveHelper active helper i) = 0)
    (noPole : ∀ i, active i → NoSlotPole (rows i) chi)
    (inactiveWeights : ∀ i, ¬active i →
      (∀ slot, (rows i).producerWeight slot = 0) ∧
      ∀ slot, (rows i).consumerWeight slot = 0) :
    (∑ i, rationalContribution (rows i) chi) = 0 := by
  have same : (∑ i, rationalContribution (rows i) chi) =
      activeBalance active rows chi := by
    unfold activeBalance
    apply Finset.sum_congr rfl
    intro i _
    by_cases ai : active i
    · simp only [if_pos ai]
    · simp only [if_neg ai]
      exact rationalContribution_zero_weights (rows i) chi
        (inactiveWeights i ai).1 (inactiveWeights i ai).2
  rw [same]
  exact active_balance_zero_of_rows active rows helper chi
    localZero totalZero inactiveZero noPole
end Global

#print axioms publicWeight_binary
#print axioms append_weights_sum
#print axioms sourceResidual_eq_expanded
#print axioms helper_eq_rational_of_source_zero
#print axioms zero_weight_pole_regression
#print axioms active_balance_zero_of_rows
#print axioms whole_balance_zero_of_rows
end AspisV8.SelectedWeightedCopyCore
