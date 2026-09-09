import SelectedCoveredRelation
import SelectedComponentGame
import FixedC1HelperReduction

/-! The selected 26+3 execution with NO supplied C1 message, early decoder
success or received polynomiality premise. The complete compact-suffix mass
splits exactly into absence/presence of a good quotient representative.
The latter is retained, not renamed payment extraction. Gamma is averaged
without another root charge; all downstream choices remain causal. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 300000
namespace AspisV8.CausalCoveredRecovery
open Finset Polynomial
open AspisV8.SelectedReceivedOracle AspisV8.SelectedCoveredRelation
open AspisV8.CausalOrderedRelation AspisV8.JointImageGame
open AspisV8.RelationCompatibleMoment AspisV8.ShiftedRowPrefix
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
open AspisV8.OODInterpolant AspisV8.GammaComponentGame
open AspisV8.FixedC1HelperReduction AspisV8.ClaimTransport
open AspisPool.V7C1ConcreteProjectionBinding
noncomputable section
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero
local instance : Fintype (Fin 262144) := AspisV8.EarlyC1Specialization.explicit_instance
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P

/-- C1 is fixed first; C2 may depend on earlier lambda/chi. Both words,
ordinary component claims and OOD data precede gamma. The inactive claim may
depend on gamma; Strategy preserves kappa/tau/alpha/query/rho ordering.
No finite-root commitment is itself asserted to supply these total words. -/
structure Execution (q : Nat) where
  c1 : C1Received
  c2 : C2Received
  data : Data (K := K)
  quarter : K
  quarterChecked : quarter*4=1
  weights : Fin 4 → Fin 1024 → K
  claims : Fin 3 → Fin 29 → K
  inactive : K → K
  strategy : K → K → Strategy domain q

def Execution.raw {q : Nat} (e : Execution q) (gamma : K) : Fin 1048576 → K :=
  SelectedComponentGame.received e.c1 e.c2 e.data gamma

def Execution.rows {q : Nat} (e : Execution q) (gamma : K) : Rows (K := K) :=
  rowPrefix e.data e.quarter e.weights e.claims e.inactive gamma

/-- Actual construction establishes the oracle reference boundary. -/
theorem row_reference_zero {q : Nat} (e : Execution q) (gamma : K) :
    (e.rows gamma).referenceQ=0 := rfl

def goodPrefix {q : Nat} (e : Execution q) (gamma kappa tau alpha : K) : Prop :=
  goodCovered (e.rows gamma) (e.raw gamma) alpha ((e.strategy gamma kappa).final tau alpha)

def suffix {q : Nat} (e : Execution q) (gamma kappa tau alpha : K)
    (A G : Finset K) : ℚ :=
  (after ((e.rows gamma).before kappa) e.quarterChecked
    (oracle 0 (e.raw gamma)) (e.strategy gamma kappa) tau alpha).prob A G

def missingSlice {q : Nat} (e : Execution q) (gamma : K) (A G : Finset K) : ℚ :=
  avg G (fun kappa => avg G (fun tau => avg A (fun alpha =>
    if ¬goodPrefix e gamma kappa tau alpha then suffix e gamma kappa tau alpha A G else 0)))

def goodSlice {q : Nat} (e : Execution q) (gamma : K) (A G : Finset K) : ℚ :=
  avg G (fun kappa => avg G (fun tau => avg A (fun alpha =>
    if goodPrefix e gamma kappa tau alpha then suffix e gamma kappa tau alpha A G else 0)))

def totalSlice {q : Nat} (e : Execution q) (gamma : K) (A G : Finset K) : ℚ :=
  avg G (fun kappa => avg G (fun tau => avg A (fun alpha =>
    suffix e gamma kappa tau alpha A G)))

def missingProbability {q : Nat} (e : Execution q) (A G Gamma : Finset K) : ℚ :=
  avg Gamma (fun gamma => missingSlice e gamma A G)

def goodProbability {q : Nat} (e : Execution q) (A G Gamma : Finset K) : ℚ :=
  avg Gamma (fun gamma => goodSlice e gamma A G)

def totalProbability {q : Nat} (e : Execution q) (A G Gamma : Finset K) : ℚ :=
  avg Gamma (fun gamma => totalSlice e gamma A G)

def ceiling (q : Nat) (A G : Finset K) : ℚ :=
  SelectedOutsideQuery.ceiling q A+99*(3/(G.card:ℚ)+6/(A.card:ℚ))+
    (q:ℚ)/G.card+18/A.card

/-- Uniform at every gamma, including arbitrary received C1 and all
early-object/provider-none mathematical branches. No gamma collision term. -/
theorem missing_slice_bound {q : Nat} (e : Execution q) (gamma : K)
    (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty)
    (positive : 0<q) (count : q≤262144) :
    missingSlice e gamma A G≤ceiling q A G := by
  have bound := no_good_quotient_bound (e.rows gamma) e.quarterChecked
    (e.raw gamma) (e.strategy gamma) A G ha hg positive count
  change missingSlice e gamma A G≤ceiling q A G at bound
  exact bound

theorem missing_bound {q : Nat} (e : Execution q) (A G Gamma : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) (hgamma : Gamma.Nonempty)
    (positive : 0<q) (count : q≤262144) :
    missingProbability e A G Gamma≤ceiling q A G := by
  exact avg_le Gamma hgamma _ _ (fun gamma _ =>
    missing_slice_bound e gamma A G ha hg positive count)

/-- Exact partition of the SAME selected compact suffix, not two separately
generated fixtures or an enlargement from bad-binding to payment failure. -/
theorem slice_partition {q : Nat} (e : Execution q) (gamma : K) (A G : Finset K) :
    totalSlice e gamma A G=missingSlice e gamma A G+goodSlice e gamma A G := by
  unfold totalSlice missingSlice goodSlice
  simp_rw [← avg_add]
  congr 1
  funext kappa
  congr 1
  funext tau
  congr 1
  funext alpha
  by_cases good : goodPrefix e gamma kappa tau alpha
  · simp only [good,not_true_eq_false,if_false,if_true,zero_add]
  · simp only [good,not_false_eq_true,if_false,if_true,add_zero]

theorem probability_partition {q : Nat} (e : Execution q) (A G Gamma : Finset K) :
    totalProbability e A G Gamma=
      missingProbability e A G Gamma+goodProbability e A G Gamma := by
  unfold totalProbability missingProbability goodProbability
  simp_rw [slice_partition]
  exact avg_add Gamma _ _

theorem total_bound {q : Nat} (e : Execution q) (A G Gamma : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) (hgamma : Gamma.Nonempty)
    (positive : 0<q) (count : q≤262144) :
    totalProbability e A G Gamma≤ceiling q A G+goodProbability e A G Gamma := by
  have partition := probability_partition e A G Gamma
  have bound := missing_bound e A G Gamma ha hg hgamma positive count
  linarith only [partition,bound]

/-- Reuse the actual unknown three-helper curve; no helper membership and
no reduction of the ordinary/OOD component error degree to two. -/
theorem helper_degree {q : Nat} (e : Execution q) (index : Fin 1048576) :
    (helperPolynomial e.c2 index).natDegree≤2 :=
  helperPolynomial_degree e.c2 index

theorem full_component_error_degree (p : Fin 29 → Message)
    (ell : Message →ₗ[K] K) (claimed : Fin 29 → K) :
    (errorPolynomial ell p claimed).natDegree≤28 :=
  component_error_degree ell p claimed

#print axioms row_reference_zero
#print axioms missing_slice_bound
#print axioms missing_bound
#print axioms slice_partition
#print axioms probability_partition
#print axioms total_bound
#print axioms helper_degree
#print axioms full_component_error_degree
end
end AspisV8.CausalCoveredRecovery
