import ThreeHelperClaimCover
import HigherYRegularBranch
import SelectedLinearCover

/-! Fixed-early-C1 high-support higher-Y counting. The old three-helper
dichotomy constructs the actual message tuple BEFORE OOD/gamma; its sparse
branch is charged, not removed. Prime-factor root counts are added through
their weights, not multiplied by the number of factors. No regularity,
pre-alpha final, or gamma/query probability product is assumed.
Source-review draft only.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.EarlyC1HigherYSupport
open Polynomial Finset
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementFactorBudgets
open AspisV8.HigherYCurveObstruction
noncomputable section
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P

namespace Generic
variable {K : Type*} [Field K]

def coherentHits (factors : Multiset (TrivariatePolynomial K))
    (curve : Polynomial K[X]) (Gamma : Finset K) : Finset K :=
  Gamma.filter fun gamma => ∃ F ∈ factors, 3 ≤ F.natDegree ∧
    challengeCandidateHom gamma (curve.eval (C gamma)) F=0

/-- Repeated factors remain in the weight sum. The union need not be
disjoint and the factor may be chosen arbitrarily at each gamma. -/
theorem coherent_multiset_count (c : Nat)
    (factors : Multiset (TrivariatePolynomial K))
    (primes : ∀ F ∈ factors, Prime F) (curve : Polynomial K[X])
    (small : curve.natDegree ≤ c) (Gamma : Finset K) :
    (coherentHits factors curve Gamma).card ≤
      (factors.map (trivariateYZWeight c)).sum := by
  classical
  induction factors using Multiset.induction_on with
  | empty => simp [coherentHits]
  | @cons F rest ih =>
      have tail := ih (fun J member => primes J (Multiset.mem_cons_of_mem member))
      by_cases higher : 3 ≤ F.natDegree
      · let one := Gamma.filter fun gamma =>
          challengeCandidateHom gamma (curve.eval (C gamma)) F=0
        have first : one.card ≤ trivariateYZWeight c F :=
          coherent_specializations_card c F (primes F (Multiset.mem_cons_self F rest))
            (by omega) curve small one (fun _ member => (Finset.mem_filter.mp member).2)
        have inclusion : coherentHits (F ::ₘ rest) curve Gamma ⊆
            one ∪ coherentHits rest curve Gamma := by
          intro gamma member
          obtain ⟨inGamma, J, member, high, root⟩ := Finset.mem_filter.mp member
          rcases Multiset.mem_cons.mp member with same | member
          · subst J
            exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨inGamma, root⟩)
          · exact Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨inGamma, J, member, high, root⟩)
        simpa only [Multiset.map_cons, Multiset.sum_cons] using
          (Finset.card_le_card inclusion).trans
            ((Finset.card_union_le one _).trans (Nat.add_le_add first tail))
      · have inclusion : coherentHits (F ::ₘ rest) curve Gamma ⊆
            coherentHits rest curve Gamma := by
          intro gamma member
          obtain ⟨inGamma, J, member, high, root⟩ := Finset.mem_filter.mp member
          rcases Multiset.mem_cons.mp member with same | member
          · subst J
            exact False.elim (higher high)
          · exact Finset.mem_filter.mpr ⟨inGamma, J, member, high, root⟩
        simpa only [Multiset.map_cons, Multiset.sum_cons] using
          ((Finset.card_le_card inclusion).trans tail).trans (Nat.le_add_left _ _)

theorem coherent_parent_count (c : Nat) (P : TrivariatePolynomial K)
    (nonzero : P ≠ 0) (curve : Polynomial K[X]) (small : curve.natDegree ≤ c)
    (Gamma : Finset K) :
    (coherentHits (curvePrimeFactors P) curve Gamma).card ≤ trivariateYZWeight c P :=
  (coherent_multiset_count c (curvePrimeFactors P)
    (fun F member => curvePrimeFactors_prime P nonzero F member) curve small Gamma).trans
      (AspisV8.FactorIdentityCover.all_factor_weights_le c P nonzero)

theorem coefficientCurve_linear_eval {M : Type*} [AddCommGroup M] [Module K M]
    (encode : M →ₗ[K] K[X]) (messages : Fin 29 → M) (gamma : K) :
    (HigherYRegularBranch.Generic.coefficientCurve (c := 28)
      (fun lane => encode (messages lane))).eval (C gamma) =
        encode (ClaimTransport.batch gamma messages) := by
  rw [HigherYRegularBranch.Generic.coefficientCurve_eval, ClaimTransport.batch, map_sum]
  simp only [map_smul]

end Generic

abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact

open AspisV8.SelectedReceivedOracle AspisV8.SelectedOODGate
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
open AspisV8.PartialFoldRecovery AspisV8.SelectedFactorCoherence
open AspisV8.ThreeHelperClaimCover AspisV8.GammaComponentGame
open AspisV8.OODInterpolant AspisV8.FactorIdentityCover
open AspisPool.V7C1ConcreteProjectionBinding
open AspisK1.V7Tag73ExactGRSConversion
noncomputable section
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero
attribute [local irreducible] curvePrimeFactors

def tupleCurve (messages : Fin 29 → Message) : Polynomial K[X] :=
  HigherYRegularBranch.Generic.coefficientCurve (c := 28)
    (fun lane => SelectedGRSSubmodule.encoder (messages lane))

theorem tupleCurve_eval (messages : Fin 29 → Message) (gamma : K) :
    (tupleCurve messages).eval (C gamma)=
      exactCircleGRSPolynomial (ClaimTransport.batch gamma messages) :=
  (Generic.coefficientCurve_linear_eval SelectedGRSSubmodule.encoder messages gamma).trans
    (SelectedGRSSubmodule.encoder_eq _)

/-- The output of the existing causal cover, not an extra correspondence
premise at the final endpoint. In particular d is quantified AFTER messages. -/
def Covers (c1 : C1Received) (c2 : C2Received) (Gamma : Finset K)
    (messages : Fin 29 → Message) : Prop :=
  ∀ d : Data (K := K), d.Checked → ∀ gamma ∈ Gamma, ∀ Q : Message,
    (Q 1023=0 ∧ d.b*Q 1022-d.c*Q 1021=0) →
    (fibreBad (m := 262144) (exactInitialEncoder Q)
      (SelectedQuotientOriginal.virtual d
        (AspisV8.NearGammaSelectedC1.rawBatch c1 c2 gamma))).card ≤ 4*15334 →
    d.original Q=ClaimTransport.batch gamma messages

/-- Every image-valid high-support quotient is allowed; no supplied
literal-family membership or fixed choice Q(gamma) is required. Retained
factors use the actual OOD prefix. No regular derivative premise is used. -/
def highHigherGammas (c1 : C1Received) (c2 : C2Received) (d : Data (K := K))
    (Gamma : Finset K) : Finset K :=
  Gamma.filter fun gamma => ∃ Q : Message,
    (Q 1023=0 ∧ (atGamma d gamma).b*Q 1022-(atGamma d gamma).c*Q 1021=0) ∧
    (fibreBad (m := 262144) (exactInitialEncoder Q)
      (SelectedComponentGame.received c1 c2 d gamma)).card ≤ 4*15334 ∧
    ∃ F ∈ curvePrimeFactors (parent c1 c2), 3 ≤ F.natDegree ∧
      Retained (point d) (fun r => CurveOODGate.answerCurve (answers d r)) F ∧
      challengeCandidateHom gamma
        (exactCircleGRSPolynomial ((atGamma d gamma).original Q)) F=0

theorem covered_high_count (c1 : C1Received) (c2 : C2Received) (Gamma : Finset K)
    (messages : Fin 29 → Message) (cover : Covers c1 c2 Gamma messages)
    (d : Data (K := K)) (checked : d.Checked) :
    (highHigherGammas c1 c2 d Gamma).card ≤ 117077 := by
  have inclusion : highHigherGammas c1 c2 d Gamma ⊆
      Generic.coherentHits (curvePrimeFactors (parent c1 c2)) (tupleCurve messages) Gamma := by
    intro gamma member
    obtain ⟨inGamma, Q, image, close, F, factor, higher, _, root⟩ :=
      Finset.mem_filter.mp member
    have recovered := cover (atGamma d gamma)
      (SelectedComponentGame.checked_atGamma d checked gamma) gamma inGamma Q image close
    rw [recovered, ← tupleCurve_eval] at root
    exact Finset.mem_filter.mpr ⟨inGamma, F, factor, higher, root⟩
  have nonzero : parent c1 c2 ≠ 0 :=
    curveTrivariatePolynomial_ne_zero _ (fixedInterpolant_nonzero c1 c2)
  have small : (tupleCurve messages).natDegree ≤ 28 :=
    HigherYRegularBranch.Generic.coefficientCurve_degree _
  have bound := Generic.coherent_parent_count 28 (parent c1 c2) nonzero
    (tupleCurve messages) small Gamma
  have weight : trivariateYZWeight 28 (parent c1 c2) ≤ 117077 :=
    Nat.le_of_lt_succ (trivariateYZWeight_curveTrivariatePolynomial_lt
      (by norm_num : 0 < 117078) (fixedInterpolant c1 c2))
  exact (Finset.card_le_card inclusion).trans (bound.trans weight)

/-- C1, its actual early optional output, C2 and Gamma precede the tuple;
all OOD data and arbitrary later Q choices follow it. Sparse helper-good
gammas are retained exactly, rather than postselecting the dense branch. -/
theorem fixed_early_dichotomy (c1 : C1Received) (p : C1Messages) (c2 : C2Received)
    (Gamma : Finset K) (nonzero : ∀ gamma ∈ Gamma, gamma ≠ 0)
    (found : earlyC1 c1=some p) :
    (goodGammas c1 p c2 Gamma).card < 3 ∨
      ∃ messages : Fin 29 → Message, c1Projection messages=p ∧
        Covers c1 c2 Gamma messages ∧
        ∀ d : Data (K := K), d.Checked → (highHigherGammas c1 c2 d Gamma).card ≤ 117077 := by
  rcases quotient_cover_dichotomy c1 p c2 Gamma nonzero found with
    sparse | ⟨messages, projection, cover⟩
  · exact Or.inl sparse
  · exact Or.inr ⟨messages, projection, cover,
      fun d checked => covered_high_count c1 c2 Gamma messages cover d checked⟩

/-- The sparse and dense branches both yield the same advertised coarse
cardinality bound. This counts all retained higher roots, not acceptance. -/
theorem fixed_early_high_count (c1 : C1Received) (p : C1Messages) (c2 : C2Received)
    (Gamma : Finset K) (nonzero : ∀ gamma ∈ Gamma, gamma ≠ 0)
    (found : earlyC1 c1=some p) (d : Data (K := K)) (checked : d.Checked) :
    (highHigherGammas c1 c2 d Gamma).card ≤ 117077 := by
  rcases fixed_early_dichotomy c1 p c2 Gamma nonzero found with
    sparse | ⟨messages, projection, cover, bounded⟩
  · have inclusion : highHigherGammas c1 c2 d Gamma ⊆ goodGammas c1 p c2 Gamma := by
      intro gamma member
      obtain ⟨inGamma, Q, image, close, _⟩ := Finset.mem_filter.mp member
      exact good_of_close_image c1 p c2 Gamma gamma inGamma (nonzero gamma inGamma)
        (atGamma d gamma) (SelectedComponentGame.checked_atGamma d checked gamma) Q image close
    have bound := Finset.card_le_card inclusion
    omega
  · exact bounded d checked

#print axioms Generic.coherent_multiset_count
#print axioms Generic.coherent_parent_count
#print axioms Generic.coefficientCurve_linear_eval
#print axioms tupleCurve_eval
#print axioms covered_high_count
#print axioms fixed_early_dichotomy
#print axioms fixed_early_high_count
end
end
end AspisV8.EarlyC1HigherYSupport
