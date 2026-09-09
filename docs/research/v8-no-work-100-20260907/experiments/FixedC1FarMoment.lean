import RelationCompatibleMoment
import HelperJointGame

/-! The actual fixed-C1 far-final event reduced to the relation-compatible
agreement moment. The final remains adaptive in tau and alpha. The degree-two
helper curve and degree-28 component errors are derived, not new coverage
premises. No numeric bound on the remaining moment is asserted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 300000
namespace AspisV8.FixedC1FarMomentAux
open Finset Polynomial AspisV8.JointImageGame
variable {K : Type*} [Field K] [DecidableEq K]

/-- Retain an unknown varying continuation moment outside the roots. This
does not turn a root count into a bound on that continuation moment. -/
theorem charge_roots (Gamma : Finset K) (nonempty : Gamma.Nonempty)
    (E : K[X]) (nonzero : E≠0) (degree : E.natDegree≤28)
    (f g : K → ℚ) (collision : ℚ) (positive : 0≤collision)
    (unit : ∀ gamma∈Gamma, f gamma≤1)
    (momentNonneg : ∀ gamma∈Gamma, 0≤g gamma)
    (bound : ∀ gamma∈Gamma, E.eval gamma≠0 → f gamma≤g gamma+collision) :
    avg Gamma f≤28/Gamma.card+
      avg Gamma (fun gamma => if E.eval gamma≠0 then g gamma else 0)+collision := by
  classical
  let outside := fun gamma => if E.eval gamma≠0 then g gamma else 0
  have subtraction := avg_polynomial Gamma nonempty E nonzero 28 degree
    (fun gamma => f gamma-outside gamma) collision positive (by
      intro gamma member
      have nn : 0≤outside gamma := by
        dsimp only [outside]
        split_ifs
        · exact momentNonneg gamma member
        · exact le_refl 0
      exact (sub_le_self _ nn).trans (unit gamma member)) (by
      intro gamma member notRoot
      dsimp only [outside]
      rw [if_pos notRoot]
      exact sub_le_iff_le_add.mpr (by
        simpa only [add_comm] using bound gamma member notRoot))
  have split : avg Gamma (fun gamma => f gamma-outside gamma)=
      avg Gamma f-avg Gamma outside := by
    simp only [avg,Finset.sum_sub_distrib,sub_div]
  rw [split] at subtraction
  dsimp only [outside] at subtraction
  linarith
end AspisV8.FixedC1FarMomentAux

namespace AspisV8.FixedC1FarMoment
open Finset Polynomial
open AspisV8.SelectedReceivedOracle AspisV8.GammaComponentGame
open AspisV8.SelectedComponentGame AspisV8.ComponentOODBinding
open AspisV8.OODInterpolant AspisV8.CausalOrderedRelation
open AspisV8.ShiftedRowPrefix AspisV8.JointImageGame AspisV8.ClaimTransport
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
open AspisV8.ThreeHelperClaimCover AspisV8.FixedC1HelperReduction
open AspisPool.V7C1ConcreteProjectionBinding
noncomputable section
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero
local instance : Fintype (Fin 262144) := AspisV8.EarlyC1Specialization.explicit_instance
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P

/-- C1 and its optional identification are fixed first. C2 may have depended
on earlier semantic challenges but not on gamma. The OOD answers and ordinary
claims are also fixed before gamma. Inactive knows gamma; the later strategy
knows gamma/kappa, with its own first-response/final/tail causal interfaces. -/
structure Execution (q : Nat) where
  c1 : C1Received
  p : C1Messages
  found : earlyC1 c1=some p
  c2 : C2Received
  data : Data (K := K)
  quarter : K
  quarterChecked : quarter*4=1
  weights : Fin 4 → Fin 1024 → K
  claims : Fin 3 → Fin 29 → K
  inactive : K → K
  strategy : K → K → Strategy domain q

def Execution.wrongC1 {q : Nat} (e : Execution q) : Prop :=
  (∃ (j : Fin 3) (lane : Fin 26),
    e.claims j (Fin.castAdd 3 lane)≠covector (e.weights j.succ) (e.p lane)) ∨
  ∃ (r : Fin 2) (lane : Fin 26),
    e.data.answers r (Fin.castAdd 3 lane)≠
      circleFunctional (pointX e.data r) (pointY e.data r) (e.p lane)

def Execution.raw {q : Nat} (e : Execution q) (gamma : K) : Fin 1048576 → K :=
  received e.c1 e.c2 e.data gamma

def Execution.rows {q : Nat} (e : Execution q) (gamma : K) : Rows (K := K) :=
  rowPrefix e.data e.quarter e.weights e.claims e.inactive gamma

def Execution.farWrong {q : Nat} (e : Execution q) (gamma kappa tau alpha : K) : Prop :=
  e.wrongC1 ∧ ¬PreAnchorJoint.near (e.raw gamma) 15334 (e.strategy gamma) kappa tau alpha

def Execution.sliceProbability {q : Nat} (e : Execution q)
    (gamma kappa : K) (A G : Finset K) : ℚ :=
  avg G (fun tau => avg A (fun alpha => if e.farWrong gamma kappa tau alpha then
    (after ((e.rows gamma).before kappa) e.quarterChecked
      (oracle 0 (e.raw gamma)) (e.strategy gamma kappa) tau alpha).prob A G else 0))

/-- The carried prior uses the ACTUAL chosen final, transported original
functional, carried image weights, and first compact response. It is not the
old prior evaluated against a true fold or an anchor selected after alpha. -/
def Execution.sliceMoment {q : Nat} (e : Execution q)
    (gamma kappa : K) (A G : Finset K) : ℚ :=
  avg G (fun tau => avg A (fun alpha => if e.farWrong gamma kappa tau alpha then
    RelationCompatibleMoment.compatibleMoment
      (atFold ((e.rows gamma).before kappa) (e.strategy gamma kappa) tau alpha)
      ((e.strategy gamma kappa).final tau alpha)
      ((oracle 0 (e.raw gamma)).folded alpha) domain q else 0))

def Execution.farProbability {q : Nat} (e : Execution q) (A G Gamma : Finset K) : ℚ :=
  avg Gamma (fun gamma => avg G (fun kappa => e.sliceProbability gamma kappa A G))

def Execution.farMoment {q : Nat} (e : Execution q) (A G Gamma : Finset K) : ℚ :=
  avg Gamma (fun gamma => avg G (fun kappa => e.sliceMoment gamma kappa A G))

def Execution.outsideRootMoment {q : Nat} (e : Execution q) (E : K[X])
    (A G Gamma : Finset K) : ℚ :=
  avg Gamma (fun gamma => if E.eval gamma≠0 then
    avg G (fun kappa => e.sliceMoment gamma kappa A G) else 0)

/-- The source scalar-power helper curve is exactly quadratic at every
stored symbol, independently of whether any helper lane is a codeword. -/
theorem helper_degree {q : Nat} (e : Execution q) (index : Fin 1048576) :
    (helperPolynomial e.c2 index).natDegree≤2 :=
  helperPolynomial_degree e.c2 index

/-- On C1's own support, the literal raw batch is known-C1 plus gamma^26
times the quadratic helper curve. The excluded C1 fibres remain in the game. -/
theorem raw_on_own_support {q : Nat} (e : Execution q) (gamma : K)
    (f : Fin 262144) (hf : f∈ownSupport e.c1 e.p) (slot : Fin 4) :
    AspisV8.NearGammaSelectedC1.rawBatch e.c1 e.c2 gamma (AspisV8.NearGammaFibreBridge.fibreEmbed (f,slot))=
      exactInitialEncoder (c1Batch e.p gamma) (AspisV8.NearGammaFibreBridge.fibreEmbed (f,slot))+
        gamma^26*(helperPolynomial e.c2 (AspisV8.NearGammaFibreBridge.fibreEmbed (f,slot))).eval gamma := by
  rw [raw_batch_on_c1_support e.c1 e.p e.c2 gamma _
    (ownSupport_same e.c1 e.p f hf slot)]
  rw [raw_batch_split,helperPolynomial_eval]

/-- Every arbitrary pre-gamma helper MESSAGE triple preserves a wrong C1
coefficient in the full degree-28 error polynomial. This does not assert that
the triple represents the received helpers or an adaptive far final. -/
theorem joined_error_nonzero_degree (p : C1Messages) (h : Fin 3 → Message)
    (ell : Message →ₗ[K] K) (claims : Fin 29 → K) (lane : Fin 26)
    (wrong : claims (Fin.castAdd 3 lane)≠ell (p lane)) :
    errorPolynomial ell (join p h) claims≠0 ∧
      (errorPolynomial ell (join p h) claims).natDegree≤28 := by
  constructor
  · apply component_error_nonzero ell (join p h) claims (Fin.castAdd 3 lane)
    simpa only [join_left] using wrong
  · exact component_error_degree ell (join p h) claims

/-- Select one genuinely wrong ordinary/OOD row before gamma. Its error
polynomial remains nonzero of degree at most 28 for EACH helper triple,
without a 145-claim union and without claiming a bounded covering family. -/
theorem wrong_claim_polynomials {q : Nat} (e : Execution q) (wrong : e.wrongC1) :
    ∃ (ell : Message →ₗ[K] K) (claims : Fin 29 → K),
      ∀ h : Fin 3 → Message,
        errorPolynomial ell (join e.p h) claims≠0 ∧
          (errorPolynomial ell (join e.p h) claims).natDegree≤28 := by
  rcases wrong with ⟨j,lane,bad⟩ | ⟨r,lane,bad⟩
  · exact ⟨covector (e.weights j.succ),e.claims j,
      fun h => joined_error_nonzero_degree e.p h _ _ lane bad⟩
  · exact ⟨circleFunctional (pointX e.data r) (pointY e.data r),e.data.answers r,
      fun h => joined_error_nonzero_degree e.p h _ _ lane bad⟩

theorem slice_bound {q : Nat} (e : Execution q) (gamma kappa : K)
    (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty)
    (positive : 0<q) (count : q≤domain.card) :
    e.sliceProbability gamma kappa A G≤
      e.sliceMoment gamma kappa A G+(q:ℚ)/G.card+18/A.card := by
  exact RelationCompatibleMoment.causal_supported_bound
    ((e.rows gamma).before kappa) e.quarterChecked (oracle 0 (e.raw gamma))
    (e.strategy gamma kappa) (e.farWrong gamma kappa) A G ha hg positive count

/-- A reduction of the accepted far/wrong-C1 event, not a numerical upper
bound on its remaining agreement moment. Gamma/kappa/tau/alpha remain fresh
sequential averages; no post-challenge final is moved before alpha. Only the
degree-q rho cancellation and THREE later relation repairs are charged here.
The image mix, shifted rows and first relation response remain in the moment. -/
theorem far_wrong_reduction {q : Nat} (e : Execution q) (A G Gamma : Finset K)
    (ha : A.Nonempty) (hg : G.Nonempty) (hgamma : Gamma.Nonempty)
    (positive : 0<q) (count : q≤domain.card) :
    e.farProbability A G Gamma≤e.farMoment A G Gamma+(q:ℚ)/G.card+18/A.card := by
  have rowBound (gamma : K) :
      avg G (fun kappa => e.sliceProbability gamma kappa A G)≤
        avg G (fun kappa => e.sliceMoment gamma kappa A G)+((q:ℚ)/G.card+18/A.card) := by
    have h := RelationCompatibleMoment.avg_mono G _ _ (fun kappa _ =>
      show e.sliceProbability gamma kappa A G≤
        e.sliceMoment gamma kappa A G+((q:ℚ)/G.card+18/A.card) by
        simpa only [add_assoc] using slice_bound e gamma kappa A G ha hg positive count)
    rw [RelationCompatibleMoment.avg_add,RelationCompatibleMoment.avg_constant G hg] at h
    exact h
  have h := RelationCompatibleMoment.avg_mono Gamma _ _ (fun gamma _ => rowBound gamma)
  rw [RelationCompatibleMoment.avg_add,RelationCompatibleMoment.avg_constant Gamma hgamma] at h
  simpa only [Execution.farProbability,Execution.farMoment,add_assoc] using h

theorem row_probability_unit {q : Nat} (e : Execution q) (gamma : K)
    (A G : Finset K) (ha : A.Nonempty) (hg : G.Nonempty) (count : q≤domain.card) :
    avg G (fun kappa => e.sliceProbability gamma kappa A G)≤1 := by
  apply avg_le G hg
  intro kappa _
  exact AspisV8.RepresentedImageGame.supported_unit ((e.rows gamma).before kappa)
    e.quarterChecked (oracle 0 (e.raw gamma)) (e.strategy gamma kappa)
    (e.farWrong gamma kappa) A G ha hg count

theorem row_moment_nonneg {q : Nat} (e : Execution q) (gamma : K)
    (A G : Finset K) : 0≤avg G (fun kappa => e.sliceMoment gamma kappa A G) := by
  apply avg_nonneg
  intro kappa _
  apply avg_nonneg
  intro tau _
  apply avg_nonneg
  intro alpha _
  split_ifs
  · unfold RelationCompatibleMoment.compatibleMoment
    split_ifs
    · unfold RelationCompatibleMoment.matchingRatio
      positivity
    · exact le_refl 0
  · exact le_refl 0

/-- Fixed early C1 picks one false claim, not a post-gamma target. For any
fixed helper message triple its at most 28 root gammas are charged. The
remaining moment explicitly excludes those roots, but is NOT given a bound.
The supplied helper message triple need not cover the actual helper oracle.
This restriction retains the actual arbitrary three-helper received word. -/
theorem fixed_claim_far_reduction {q : Nat} (e : Execution q) (wrong : e.wrongC1)
    (A G Gamma : Finset K) (ha : A.Nonempty) (hg : G.Nonempty)
    (hgamma : Gamma.Nonempty) (positive : 0<q) (count : q≤domain.card) :
    ∃ (ell : Message →ₗ[K] K) (claims : Fin 29 → K),
      ∀ h : Fin 3 → Message,
        let E := errorPolynomial ell (join e.p h) claims
        E≠0 ∧ E.natDegree≤28 ∧
          e.farProbability A G Gamma≤28/Gamma.card+
            e.outsideRootMoment E A G Gamma+(q:ℚ)/G.card+18/A.card := by
  obtain ⟨ell,claims,errors⟩ := wrong_claim_polynomials e wrong
  refine ⟨ell,claims,?_⟩
  intro h
  refine ⟨(errors h).1,(errors h).2,?_⟩
  have bound := FixedC1FarMomentAux.charge_roots Gamma hgamma
    (errorPolynomial ell (join e.p h) claims) (errors h).1 (errors h).2
    (fun gamma => avg G (fun kappa => e.sliceProbability gamma kappa A G))
    (fun gamma => avg G (fun kappa => e.sliceMoment gamma kappa A G))
    ((q:ℚ)/G.card+18/A.card) (by positivity)
    (fun gamma _ => row_probability_unit e gamma A G ha hg count)
    (fun gamma _ => row_moment_nonneg e gamma A G) (by
      intro gamma _ _
      have localBound := RelationCompatibleMoment.avg_mono G _ _ (fun kappa _ =>
        show e.sliceProbability gamma kappa A G≤
          e.sliceMoment gamma kappa A G+((q:ℚ)/G.card+18/A.card) by
          simpa only [add_assoc] using slice_bound e gamma kappa A G ha hg positive count)
      rw [RelationCompatibleMoment.avg_add,RelationCompatibleMoment.avg_constant G hg] at localBound
      exact localBound)
  simpa only [Execution.farProbability,Execution.outsideRootMoment,add_assoc] using bound

#print axioms AspisV8.FixedC1FarMomentAux.charge_roots
#print axioms helper_degree
#print axioms raw_on_own_support
#print axioms joined_error_nonzero_degree
#print axioms wrong_claim_polynomials
#print axioms slice_bound
#print axioms far_wrong_reduction
#print axioms row_probability_unit
#print axioms row_moment_nonneg
#print axioms fixed_claim_far_reduction
end
end AspisV8.FixedC1FarMoment
