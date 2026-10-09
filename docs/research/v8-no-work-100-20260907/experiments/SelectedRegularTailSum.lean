import SelectedHigherYRegularTail
import SelectedSingularOODFamily

/-! Additive regular support-tail counts on ONE fixed OOD row. The left
side sums factor cardinalities, not only a union: this also controls the
alpha correction in a later sum of restricted matching moments. Factors
retain their multiset multiplicities; no disjointness or fixed selected F
is assumed. No sampler or layer-cake theorem is asserted here.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.SelectedRegularTailSum
open Polynomial Finset
noncomputable section

namespace Generic

theorem sum_scaled {I : Type*} (s : Multiset I) (value : I → Nat) (c : Nat) :
    (s.map (fun i => c*value i)).sum=c*(s.map value).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons i s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, ih, Nat.mul_add]

theorem filtered_sum_le {I : Type*} (s : Multiset I)
    (predicate : I → Prop) [DecidablePred predicate] (weight : I → Nat) :
    ((s.filter predicate).map weight).sum ≤ (s.map weight).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons i s ih =>
      by_cases h : predicate i
      · simpa only [Multiset.filter_cons_of_pos s h, Multiset.map_cons, Multiset.sum_cons]
          using Nat.add_le_add_left ih (weight i)
      · simpa only [Multiset.filter_cons_of_neg s h, Multiset.map_cons, Multiset.sum_cons]
          using ih.trans (Nat.le_add_left _ _)

/-- Linear budget identity, with one subtraction for EACH occurrence. -/
theorem affine_sum {I : Type*} (s : Multiset I) (cost weight : I → Nat)
    (offset scale : Nat)
    (individual : ∀ i ∈ s, cost i+offset=scale*weight i) :
    (s.map cost).sum+offset*s.card=scale*(s.map weight).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons i s ih =>
      have first := individual i (Multiset.mem_cons_self i s)
      have rest := ih (fun j member => individual j (Multiset.mem_cons_of_mem member))
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
      nlinarith only [first, rest]

end Generic

open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementFactorBudgets
open AspisV8.SelectedReceivedOracle AspisV8.SelectedOODGate
open AspisV8.SelectedFactorCoherence AspisV8.SelectedHigherYRegularTail
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
open AspisV8.OODInterpolant AspisV8.FactorIdentityCover
open AspisV8.SingularOODFamily
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P
attribute [local irreducible] curvePrimeFactors

/-- Fixed C1/C2 higher factors; empty and repeated-factor cases included. -/
theorem selected_budget_sum (c1 : C1Received) (c2 : C2Received) :
    ((higherFactors (parent c1 c2)).map HigherYRegularBranch.budget).sum ≤ 239599331 := by
  let s := higherFactors (parent c1 c2)
  have nonzero : parent c1 c2 ≠ 0 :=
    curveTrivariatePolynomial_ne_zero _ (fixedInterpolant_nonzero c1 c2)
  have weights : (s.map (trivariateYZWeight 28)).sum ≤ 117077 := by
    have filtered := Generic.filtered_sum_le (curvePrimeFactors (parent c1 c2))
      (fun F => 3 ≤ F.natDegree) (trivariateYZWeight 28)
    have parentBound : trivariateYZWeight 28 (parent c1 c2) ≤ 117077 :=
      Nat.le_of_lt_succ (trivariateYZWeight_curveTrivariatePolynomial_lt
        (by norm_num : 0 < 117078) (fixedInterpolant c1 c2))
    exact filtered.trans ((all_factor_weights_le 28 (parent c1 c2) nonzero).trans parentBound)
  have identity : (s.map HigherYRegularBranch.budget).sum+57288*s.card=
      2047*(s.map (trivariateYZWeight 28)).sum := by
    apply Generic.affine_sum
    intro F member
    have higher : 3 ≤ F.natDegree := (Multiset.mem_filter.mp member).2
    have lower := positive_weight 28 F (by omega)
    rw [HigherYRegularBranch.budget_formula]
    omega
  change (s.map HigherYRegularBranch.budget).sum ≤ 239599331
  by_cases empty : s=0
  · simp only [empty, Multiset.map_zero, Multiset.sum_zero, Nat.zero_le]
  · have positive : 0<s.card := by
      apply Nat.pos_of_ne_zero
      intro cardZero
      exact empty (Multiset.card_eq_zero.mp cardZero)
    omega

def tailSum (c1 : C1Received) (c2 : C2Received) (d : Data (K := K))
    (r : Fin 2) (Gamma : Finset K) (M : Nat) : Nat :=
  ((higherFactors (parent c1 c2)).map fun F =>
    if Retained (point d) (fun row => CurveOODGate.answerCurve (answers d row)) F then
      (supportGammas c1 c2 d F r Gamma M).card else 0).sum

/-- A multiplicity-preserving sum of the actual selected support tails.
The common row is fixed before gamma; both-row unioning is not implicit. -/
theorem tail_sum_bound (c1 : C1Received) (c2 : C2Received)
    (d : Data (K := K)) (checked : d.Checked)
    (circles : d.x0^2+d.y0^2=1 ∧ d.x1^2+d.y1^2=1)
    (west : ∀ r, ComponentOODBinding.pointX d r ≠ -1)
    (r : Fin 2) (Gamma : Finset K) (M : Nat) :
    (M-1024)*tailSum c1 c2 d r Gamma M ≤ 1048576*239599331 := by
  let s := higherFactors (parent c1 c2)
  let size := fun F =>
    if Retained (point d) (fun row => CurveOODGate.answerCurve (answers d row)) F then
      (supportGammas c1 c2 d F r Gamma M).card else 0
  have individual : ∀ F ∈ s, (M-1024)*size F ≤ 1048576*HigherYRegularBranch.budget F := by
    intro F member
    obtain ⟨factor, higher⟩ := Multiset.mem_filter.mp member
    by_cases retained : Retained (point d)
        (fun row => CurveOODGate.answerCurve (answers d row)) F
    · simpa only [size, if_pos retained] using
        support_tail_count c1 c2 d checked circles west F factor higher retained r Gamma M
    · simp only [size, if_neg retained, Nat.mul_zero, Nat.zero_le]
  have summed := Multiset.sum_map_le_sum_map _ _ individual
  rw [Generic.sum_scaled, Generic.sum_scaled] at summed
  exact summed.trans (Nat.mul_le_mul_left 1048576 (selected_budget_sum c1 c2))

/-- At the literal-family minimum this sum also controls all per-factor
regular gamma counts. This is the numerator needed for the alpha correction. -/
theorem minimum_tail_sum (c1 : C1Received) (c2 : C2Received)
    (d : Data (K := K)) (checked : d.Checked)
    (circles : d.x0^2+d.y0^2=1 ∧ d.x1^2+d.y1^2=1)
    (west : ∀ r, ComponentOODBinding.pointX d r ≠ -1)
    (r : Fin 2) (Gamma : Finset K) :
    37206*tailSum c1 c2 d r Gamma 38230 ≤ 1048576*239599331 :=
  tail_sum_bound c1 c2 d checked circles west r Gamma 38230

#print axioms Generic.sum_scaled
#print axioms Generic.filtered_sum_le
#print axioms Generic.affine_sum
#print axioms selected_budget_sum
#print axioms tail_sum_bound
#print axioms minimum_tail_sum
end
end AspisV8.SelectedRegularTailSum
