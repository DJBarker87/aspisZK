import RootSetPairMass
import SelectedSingularOODFamily

/-! The selected higher-Y singular obstruction's two-OOD alternative as one
fixed admissible root set.  This composes the checked root-set sampler kernel
with the selected obstruction degree.  The history-uniform oracle law remains
an explicit premise; no Fiat--Shamir freshness follows here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 300
set_option maxHeartbeats 150000

namespace AspisV8.SelectedSingularPairMass
open Polynomial Finset
open AspisV5ComponentCQM31TowerExact
open AspisV8.RootSetPairMass AspisV8.NestedCircleMass
open AspisV8.SecureCircleParameterDomain
open AspisV8.SelectedReceivedOracle AspisV8.SelectedOODGate
open AspisV8.SelectedSingularOODFamily
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
noncomputable section

/-- The complete admissible root set exists and is determined by C1/C2 before
either OOD draw.  This is finite-set construction, not sampler conditioning. -/
theorem exists_complete_root_set (c1 : C1Received) (c2 : C2Received) :
    ∃ S : Finset K, ∀ t,
      t ∈ S ↔ Admissible t ∧ (obstruction c1 c2).eval t = 0 := by
  classical
  refine ⟨Finset.univ.filter (fun t =>
    Admissible t ∧ (obstruction c1 c2).eval t = 0), ?_⟩
  intro t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

variable {O H : Type*}

/-- Abort-preserving ideal mass of the complete selected singular pair-root
alternative. `complete` merely identifies the fixed finite set; it does not
assume sampler success or condition away aborts. -/
theorem selected_pair_root_mass_numeric_le (coins : Finset O)
    (draw : H → O → Option (K × H)) (between : K → H → H)
    (law : NestedCircleMass.Generic.Uniform coins draw
      (ordinaryAtomMass (FiniteOptionMass.successMass OrdinaryPrefixMass.value)))
    (c1 : C1Received) (c2 : C2Received) (S : Finset K)
    (complete : ∀ t, t ∈ S ↔
      Admissible t ∧ (obstruction c1 c2).eval t = 0) (h : H) :
    targetMass coins draw between S h ≤
      (25345827 : ℚ) * 25345826 /
        ((domainSize : ℚ) * ((domainSize : ℚ) - 1)) := by
  have nonzero := (SelectedSingularOODFamily.fixed_cover c1 c2).1
  have cardBoundNat : S.card ≤ 25345827 := by
    apply (Polynomial.card_le_degree_of_subset_roots (p := obstruction c1 c2) ?_).trans
      (SelectedSingularOODFamily.fixed_cover c1 c2).2.1
    intro t member
    exact (Polynomial.mem_roots nonzero).mpr ((complete t).mp member).2
  have mass := actual_one_call_target_bound coins draw between law S
    (fun t member => ((complete t).mp member).1) h
  refine mass.trans ?_
  have cardBound : (S.card : ℚ) ≤ 25345827 := by exact_mod_cast cardBoundNat
  have cardNonnegative : (0 : ℚ) ≤ S.card := Nat.cast_nonneg _
  have degreeOne : (1 : ℚ) ≤ 25345827 := by norm_num
  have denominatorPositive :
      (0 : ℚ) < (domainSize : ℚ) * ((domainSize : ℚ) - 1) := by
    have domainTwo : (2 : ℚ) ≤ domainSize := by
      exact_mod_cast domain_size_bounds.2
    have domainPositive : (0 : ℚ) < domainSize := lt_of_lt_of_le (by norm_num) domainTwo
    have domainMinusOnePositive : (0 : ℚ) < (domainSize : ℚ) - 1 := by linarith
    exact mul_pos domainPositive domainMinusOnePositive
  apply div_le_div_of_nonneg_right _ (le_of_lt denominatorPositive)
  nlinarith

#print axioms exists_complete_root_set
#print axioms selected_pair_root_mass_numeric_le
end
end AspisV8.SelectedSingularPairMass
