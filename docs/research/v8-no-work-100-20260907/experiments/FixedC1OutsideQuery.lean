import FixedC1FarMoment
import SelectedOutsideQuery

/-! The actual fixed-C1/three-helper execution, with its entire off-family
compact suffix bounded uniformly in gamma and kappa. The existing degree2
helper and degree28 component-error interfaces are unchanged. Covered far
wrong-component executions remain explicit; no new gamma-root term is added.
This is not a payment-extraction or authenticated/source-FS theorem. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 300000

namespace AspisV8.FixedC1OutsideQuery
open Finset
open AspisV8.FixedC1FarMoment AspisV8.SelectedReceivedOracle
open AspisV8.CausalOrderedRelation AspisV8.JointImageGame
open AspisV8.RelationCompatibleMoment
noncomputable section
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero
local instance : Fintype (Fin 262144) := AspisV8.EarlyC1Specialization.explicit_instance
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P

/-- Derived from the actual row constructor, not supplied as a
reference/oracle correspondence hypothesis. -/
theorem row_reference_zero {q : Nat} (e : Execution q) (gamma kappa : K) :
    ((e.rows gamma).before kappa).referenceQ=0 := rfl

def outsidePrefix {q : Nat} (e : Execution q) (gamma kappa tau alpha : K) : Prop :=
  SelectedOutsideQuery.outside (e.raw gamma) alpha ((e.strategy gamma kappa).final tau alpha)

def outsideSlice {q : Nat} (e : Execution q) (gamma kappa : K) (A G : Finset K) : ℚ :=
  avg G (fun tau => avg A (fun alpha => if outsidePrefix e gamma kappa tau alpha then
    (after ((e.rows gamma).before kappa) e.quarterChecked
      (oracle 0 (e.raw gamma)) (e.strategy gamma kappa) tau alpha).prob A G else 0))

def outsideProbability {q : Nat} (e : Execution q) (A G Gamma : Finset K) : ℚ :=
  avg Gamma (fun gamma => avg G (fun kappa => outsideSlice e gamma kappa A G))

/-- Explicit remaining part of the old far/wrong-C1 event, not an assumed
extractable class. A represented quotient need not recover a valid witness. -/
def coveredFarSlice {q : Nat} (e : Execution q) (gamma kappa : K)
    (A G : Finset K) : ℚ :=
  avg G (fun tau => avg A (fun alpha =>
    if e.farWrong gamma kappa tau alpha ∧ ¬outsidePrefix e gamma kappa tau alpha then
      (after ((e.rows gamma).before kappa) e.quarterChecked
        (oracle 0 (e.raw gamma)) (e.strategy gamma kappa) tau alpha).prob A G else 0))

def coveredFarProbability {q : Nat} (e : Execution q) (A G Gamma : Finset K) : ℚ :=
  avg Gamma (fun gamma => avg G (fun kappa => coveredFarSlice e gamma kappa A G))

/-- This bounds all off-family execution mass, without requiring the
additional far/wrong-C1 predicate. The virtual word and ordinary/image prefix
are exactly those of Execution, including its gamma-dependent inactive claim. -/
theorem outside_slice_bound {q : Nat} (e : Execution q) (gamma kappa : K)
    (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty)
    (positive : 0<q) (count : q≤262144) :
    outsideSlice e gamma kappa A G≤
      SelectedOutsideQuery.ceiling q A+(q:ℚ)/G.card+18/A.card := by
  have bound := SelectedOutsideQuery.actual_off_family_suffix
    ((e.rows gamma).before kappa) e.quarterChecked (e.raw gamma) q
    (e.strategy gamma kappa) A G ha hg positive count
  -- The actual row constructor's reference is definitionally zero. Do not
  -- rewrite it inside dependent oracle/After indices and manufacture casts.
  change outsideSlice e gamma kappa A G≤
    SelectedOutsideQuery.ceiling q A+(q:ℚ)/G.card+18/A.card at bound
  exact bound

/-- Uniform source-shaped slicing permits gamma/kappa averaging with no
new root charge and no conditioning on surviving relation checks. -/
theorem all_outside_bound {q : Nat} (e : Execution q) (A G Gamma : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) (hgamma : Gamma.Nonempty)
    (positive : 0<q) (count : q≤262144) :
    outsideProbability e A G Gamma≤
      SelectedOutsideQuery.ceiling q A+(q:ℚ)/G.card+18/A.card := by
  apply avg_le Gamma hgamma
  intro gamma _
  apply avg_le G hg
  intro kappa _
  exact outside_slice_bound e gamma kappa A G ha hg positive count

theorem suffix_nonneg {q : Nat} (e : Execution q) (gamma kappa tau alpha : K)
    (A G : Finset K) (ha : A.Nonempty) :
    0≤(after ((e.rows gamma).before kappa) e.quarterChecked
      (oracle 0 (e.raw gamma)) (e.strategy gamma kappa) tau alpha).prob A G := by
  exact avg_nonneg _ _ (fun queries _ => avg_nonneg G _ (fun rho _ =>
    (rounds_unit A ha ((after ((e.rows gamma).before kappa) e.quarterChecked
      (oracle 0 (e.raw gamma)) (e.strategy gamma kappa) tau alpha).tail queries rho)).1))

/-- Pointwise event inclusion with the same actual suffix mass. The off-family
term deliberately includes more executions than the old far/wrong event. -/
theorem slice_event_partition {q : Nat} (e : Execution q) (gamma kappa : K)
    (A G : Finset K) (ha : A.Nonempty) :
    e.sliceProbability gamma kappa A G≤
      outsideSlice e gamma kappa A G+coveredFarSlice e gamma kappa A G := by
  unfold Execution.sliceProbability outsideSlice coveredFarSlice
  rw [← RelationCompatibleMoment.avg_add]
  apply avg_mono
  intro tau _
  rw [← RelationCompatibleMoment.avg_add]
  apply avg_mono
  intro alpha _
  by_cases far : e.farWrong gamma kappa tau alpha
  · by_cases out : outsidePrefix e gamma kappa tau alpha
    · have notCovered : ¬(e.farWrong gamma kappa tau alpha ∧
          ¬outsidePrefix e gamma kappa tau alpha) := fun h => h.2 out
      simp only [if_pos far,if_pos out,if_neg notCovered,add_zero,le_refl]
    · have covered : e.farWrong gamma kappa tau alpha ∧
          ¬outsidePrefix e gamma kappa tau alpha := ⟨far,out⟩
      simp only [if_pos far,if_neg out,if_pos covered,zero_add,le_refl]
  · by_cases out : outsidePrefix e gamma kappa tau alpha
    · have notCovered : ¬(e.farWrong gamma kappa tau alpha ∧
          ¬outsidePrefix e gamma kappa tau alpha) := fun h => far h.1
      simp only [if_neg far,if_pos out,if_neg notCovered,add_zero]
      exact suffix_nonneg e gamma kappa tau alpha A G ha
    · have notCovered : ¬(e.farWrong gamma kappa tau alpha ∧
          ¬outsidePrefix e gamma kappa tau alpha) := fun h => far h.1
      simp only [if_neg far,if_neg out,if_neg notCovered,add_zero,le_refl]

theorem far_event_partition {q : Nat} (e : Execution q) (A G Gamma : Finset K)
    (ha : A.Nonempty) :
    e.farProbability A G Gamma≤
      outsideProbability e A G Gamma+coveredFarProbability e A G Gamma := by
  unfold Execution.farProbability outsideProbability coveredFarProbability
  rw [← RelationCompatibleMoment.avg_add]
  apply avg_mono
  intro gamma _
  rw [← RelationCompatibleMoment.avg_add]
  apply avg_mono
  intro kappa _
  exact slice_event_partition e gamma kappa A G ha

/-- The newly bounded outside-family class plus the visibly unresolved
covered far/wrong-C1 remainder. Do not add the older28/Gamma bound again. -/
theorem far_wrong_remaining_covered {q : Nat} (e : Execution q) (A G Gamma : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) (hgamma : Gamma.Nonempty)
    (positive : 0<q) (count : q≤262144) :
    e.farProbability A G Gamma≤
      (SelectedOutsideQuery.ceiling q A+(q:ℚ)/G.card+18/A.card)+
        coveredFarProbability e A G Gamma := by
  have partition := far_event_partition e A G Gamma ha
  have outsideBound := all_outside_bound e A G Gamma ha hg hgamma positive count
  linarith only [partition,outsideBound]

#print axioms row_reference_zero
#print axioms outside_slice_bound
#print axioms all_outside_bound
#print axioms suffix_nonneg
#print axioms slice_event_partition
#print axioms far_event_partition
#print axioms far_wrong_remaining_covered
end
end AspisV8.FixedC1OutsideQuery
