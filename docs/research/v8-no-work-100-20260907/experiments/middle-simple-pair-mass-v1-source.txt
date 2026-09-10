import RootSetPairMass
import SelectedMiddleSimpleParent
import LinearDenominatorFactors

/-! Abort-preserving pair-root mass for the auxiliary middle parent.
The numerical mass theorem accepts ANY fixed E with the proved degree bound,
so a source classifier can pass its SAME existential E without identifying
two separate Classical.choose values. History-uniformity remains explicit.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.MiddleSimplePairMass
open Polynomial Finset
open AspisV5ComponentCQM31TowerExact
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementSmooth
open AspisK1.V7ExactCorrelatedAgreementFactorBudgets
open AspisV8.RootSetPairMass AspisV8.NestedCircleMass
open AspisV8.SecureCircleParameterDomain AspisV8.FactorIdentityCover
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
noncomputable section
abbrev K := QM31Exact

/-- A mathematical obstruction chosen from C1/C2 alone, before both OOD
draws. Consumers need not identify this choice with another existential E. -/
def obstruction (c1 : C1Received) (c2 : C2Received) : K[X] :=
  Classical.choose (LinearDenominatorFactors.exists_parent_obstruction 28
    (SelectedMiddleSimpleParent.parent c1 c2)
    (SelectedMiddleSimpleParent.parent_nonzero c1 c2))

theorem fixed_cover (c1 : C1Received) (c2 : C2Received) :
    obstruction c1 c2 ≠ 0 ∧ (obstruction c1 c2).natDegree ≤ 65061549 ∧
      ∀ (points : Fin 2 → K) (answers : Fin 2 → K[X])
        (F : TrivariatePolynomial K),
        F ∈ curvePrimeFactors (SelectedMiddleSimpleParent.parent c1 c2) →
        F.natDegree = 1 → Retained points answers F →
        (∀ r, (answers r).natDegree ≤ 28) →
        LinearDenominatorFactors.Small 28 F ∨
          ∀ r, (obstruction c1 c2).eval (points r) = 0 := by
  have properties := Classical.choose_spec
    (LinearDenominatorFactors.exists_parent_obstruction 28
      (SelectedMiddleSimpleParent.parent c1 c2)
      (SelectedMiddleSimpleParent.parent_nonzero c1 c2))
  have bounds := SelectedMiddleSimpleParent.parent_bounds c1 c2
  refine ⟨properties.1, properties.2.1.trans ?_, properties.2.2⟩
  calc
    _ ≤ (2*40+1)*803229 := Nat.mul_le_mul
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 bounds.2.2) 1) bounds.2.1
    _ = 65061549 := by norm_num

/-- Complete fixed admissible root set: no root or abort is conditioned away. -/
def completeRoots (E : K[X]) : Finset K := by
  classical
  exact Finset.univ.filter (fun t => Admissible t ∧ E.eval t = 0)

theorem mem_completeRoots (E : K[X]) (t : K) :
    t ∈ completeRoots E ↔ Admissible t ∧ E.eval t = 0 := by
  classical
  simp only [completeRoots, Finset.mem_filter, Finset.mem_univ, true_and]

theorem complete_roots_card (E : K[X]) (nonzero : E ≠ 0) :
    (completeRoots E).card ≤ E.natDegree := by
  apply Polynomial.card_le_degree_of_subset_roots (p := E)
  intro t member
  exact (Polynomial.mem_roots nonzero).mpr ((mem_completeRoots E t).mp member).2

variable {O H : Type*}

/-- Same-E interface for the source classifier. The one-call mass is from
the actual checked ordinary decoder, but its freshness at every history is
still the supplied law. The arbitrary between-answer history update remains. -/
theorem pair_root_mass_numeric_le (coins : Finset O)
    (draw : H → O → Option (K × H)) (between : K → H → H)
    (law : NestedCircleMass.Generic.Uniform coins draw
      (ordinaryAtomMass (FiniteOptionMass.successMass OrdinaryPrefixMass.value)))
    (E : K[X]) (nonzero : E ≠ 0) (degree : E.natDegree ≤ 65061549) (h : H) :
    targetMass coins draw between (completeRoots E) h ≤
      (65061549 : ℚ) * 65061548 /
        ((domainSize : ℚ) * ((domainSize : ℚ) - 1)) := by
  have cardBoundNat : (completeRoots E).card ≤ 65061549 :=
    (complete_roots_card E nonzero).trans degree
  have mass := actual_one_call_target_bound coins draw between law (completeRoots E)
    (fun t member => ((mem_completeRoots E t).mp member).1) h
  refine mass.trans ?_
  have cardBound : ((completeRoots E).card : ℚ) ≤ 65061549 := Nat.cast_le.mpr cardBoundNat
  have cardNonnegative : (0 : ℚ) ≤ (completeRoots E).card := Nat.cast_nonneg _
  have degreeOne : (1 : ℚ) ≤ 65061549 := by norm_num
  have denominatorPositive :
      (0 : ℚ) < (domainSize : ℚ) * ((domainSize : ℚ) - 1) := by
    have domainTwo : (2 : ℚ) ≤ domainSize := by
      exact_mod_cast domain_size_bounds.2
    have domainPositive : (0 : ℚ) < domainSize := lt_of_lt_of_le (by norm_num) domainTwo
    have domainMinusOnePositive : (0 : ℚ) < (domainSize : ℚ) - 1 := by linarith
    exact mul_pos domainPositive domainMinusOnePositive
  apply div_le_div_of_nonneg_right _ (le_of_lt denominatorPositive)
  nlinarith

/-- One actual selected-parent instantiation. This does not assert equality
between this obstruction and the E chosen by a different classifier. -/
theorem selected_pair_root_mass_numeric_le (coins : Finset O)
    (draw : H → O → Option (K × H)) (between : K → H → H)
    (law : NestedCircleMass.Generic.Uniform coins draw
      (ordinaryAtomMass (FiniteOptionMass.successMass OrdinaryPrefixMass.value)))
    (c1 : C1Received) (c2 : C2Received) (h : H) :
    targetMass coins draw between (completeRoots (obstruction c1 c2)) h ≤
      (65061549 : ℚ) * 65061548 /
        ((domainSize : ℚ) * ((domainSize : ℚ) - 1)) :=
  pair_root_mass_numeric_le coins draw between law (obstruction c1 c2)
    (fixed_cover c1 c2).1 (fixed_cover c1 c2).2.1 h

#print axioms fixed_cover
#print axioms mem_completeRoots
#print axioms complete_roots_card
#print axioms pair_root_mass_numeric_le
#print axioms selected_pair_root_mass_numeric_le
end
end AspisV8.MiddleSimplePairMass
