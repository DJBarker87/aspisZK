import SelectedMiddleSimpleParent
import MiddleLinearClassification
import MiddleGammaUnion

/-! Same-Q selected middle/high gamma capture. The auxiliary linear-Y
parent and its exceptional polynomial E are fixed from C1/C2 before OOD.
The shared gamma polynomial follows the OOD prefix but precedes gamma.
Every later Q/final choice remains existential. No early-C1 success,
regularity, component-support, gamma-nonzero or sampler premise is used.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.SelectedMiddleGammaCover
open Polynomial Finset
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisK1.V7ExactCorrelatedAgreementFactorBudgets
open AspisK1.V7Tag73ExactGRSConversion
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
open AspisV8.SelectedReceivedOracle AspisV8.SelectedFactorCoherence AspisV8.SelectedOODGate
open AspisV8.SelectedHigherYBranch AspisV8.SelectedHigherYHighSupport
open AspisV8.SelectedRegularLowSupport AspisV8.OODInterpolant AspisV8.GammaComponentGame
open AspisV8.CausalCoveredRecovery AspisV8.PartialFoldRecovery AspisV8.OffFamilyIntersection
noncomputable section
abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P
attribute [local irreducible] curvePrimeFactors

/-- The old factor can vary with gamma and Q. Retention is not needed for
this stronger gamma set, although the actual higher prefix provides it. -/
def middleGammas (c1 : C1Received) (c2 : C2Received) (d : Data (K := K))
    (Gamma : Finset K) : Finset K :=
  Gamma.filter fun gamma =>
    ∃ F ∈ curvePrimeFactors (parent c1 c2), 3 ≤ F.natDegree ∧
      ∃ Q, Qualified c1 c2 d F gamma Q ∧
        200808 ≤ fibreCount (SelectedComponentGame.received c1 c2 d gamma) Q

/-- Every fibre either matches in all four slots or has a mismatching slot.
This proves the reverse direction missing from the earlier inequality. -/
theorem full_bad_partition (received : Fin 1048576 → K) (Q : Fin 1024 → K) :
    fibreCount received Q+
      (fibreBad (m := 262144) (exactInitialEncoder Q) received).card = 262144 := by
  classical
  have disjoint : Disjoint (fullSupport univ received Q)
      (fibreBad (m := 262144) (exactInitialEncoder Q) received) := by
    apply Finset.disjoint_left.mpr
    intro i full bad
    obtain ⟨slot, different⟩ := (Finset.mem_filter.mp bad).2
    exact different ((Finset.mem_filter.mp full).2 slot)
  have cover : fullSupport univ received Q ∪
      fibreBad (m := 262144) (exactInitialEncoder Q) received = univ := by
    apply Finset.eq_univ_of_forall
    intro i
    by_cases full : ∀ slot : Fin 4,
        exactInitialEncoder Q (AspisV5ComponentCConcreteFoldLinearity.childIndex i slot)=
          received (AspisV5ComponentCConcreteFoldLinearity.childIndex i slot)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, full⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Classical.not_forall.mp full⟩)
  change (fullSupport univ received Q).card+_ = 262144
  rw [← Finset.card_union_of_disjoint disjoint, cover, Finset.card_univ, Fintype.card_fin]

/-- Actual high-prefix witnesses are middle-parent witnesses, including
the selected final and all ordinary-row gates. No candidate is replaced. -/
theorem high_prefix_mem {q : Nat} (e : Execution q) (Gamma : Finset K)
    (gamma kappa tau alpha : K) (inside : gamma ∈ Gamma)
    (high : HighPrefix e gamma kappa tau alpha) :
    gamma ∈ middleGammas e.c1 e.c2 e.data Gamma := by
  obtain ⟨Q, witness, close⟩ := high
  have image := witness_image e gamma kappa tau alpha Q witness
  have partition := full_bad_partition (e.raw gamma) Q
  have large : 200808 ≤ fibreCount (e.raw gamma) Q := by
    change (fibreBad (m := 262144) (exactInitialEncoder Q) (e.raw gamma)).card ≤ 4*15334 at close
    omega
  obtain ⟨F, member, retained, root, higher⟩ := witness.2.2.2
  exact Finset.mem_filter.mpr
    ⟨inside, F, member, higher, Q, ⟨witness.1, image, root⟩, large⟩

/-- One fixed nonzero polynomial accounts for at most forty gammas, with
the original Gamma unchanged and no division or conditioning. -/
theorem shared_roots_card (beta : K[X]) (nonzero : beta ≠ 0)
    (degree : beta.natDegree ≤ 40) (Gamma : Finset K) :
    (Gamma.filter fun gamma => beta.eval gamma=0).card ≤ 40 := by
  classical
  have roots : (Gamma.filter fun gamma => beta.eval gamma=0).val ⊆ beta.roots := by
    intro gamma member
    exact (Polynomial.mem_roots nonzero).mpr (Finset.mem_filter.mp member).2
  exact (Polynomial.card_le_degree_of_subset_roots roots).trans degree

/-- The existential E precedes both OOD rows. The SAME E must be used in
any later pair-root mass theorem. Apart from that event, all actual later
middle/high candidates together cost at most 40+28+117077 gammas. -/
theorem exists_selected_cover (c1 : C1Received) (c2 : C2Received) (Gamma : Finset K) :
    ∃ E : K[X], E ≠ 0 ∧ E.natDegree ≤ 65061549 ∧
      ∀ d : Data (K := K), d.Checked →
        (d.x0^2+d.y0^2=1 ∧ d.x1^2+d.y1^2=1) →
        (∀ r, ComponentOODBinding.pointX d r ≠ -1) →
        (∀ r, E.eval (point d r)=0) ∨ (middleGammas c1 c2 d Gamma).card ≤ 117145 := by
  classical
  have bounds := SelectedMiddleSimpleParent.parent_bounds c1 c2
  obtain ⟨E, eNonzero, eDegree, familyCard, sparseCard, classify⟩ :=
    MiddleLinearClassification.exists_classification (SelectedMiddleSimpleParent.parent c1 c2)
      (SelectedMiddleSimpleParent.parent_nonzero c1 c2)
      bounds.1 bounds.2.1 bounds.2.2 Gamma
  refine ⟨E, eNonzero, eDegree, ?_⟩
  intro d checked circles west
  by_cases pairRoot : ∀ r, E.eval (point d r)=0
  · exact Or.inl pairRoot
  · apply Or.inr
    obtain ⟨beta, betaNonzero, betaDegree, cover⟩ := classify (point d)
      (fun r => CurveOODGate.answerCurve (answers d r))
      (fun r => CurveOODGate.answerCurve_degree _)
    have nonzero : parent c1 c2 ≠ 0 :=
      curveTrivariatePolynomial_ne_zero _ (fixedInterpolant_nonzero c1 c2)
    have weight : trivariateYZWeight 28 (parent c1 c2) ≤ 117077 :=
      Nat.le_of_lt_succ (trivariateYZWeight_curveTrivariatePolynomial_lt
        (by decide : 0 < 117078) (fixedInterpolant c1 c2))
    apply MiddleGammaUnion.middle_card (parent c1 c2) nonzero weight
      EarlyC1HigherYSupport.tupleCurve
      (LinearMessageFamily.family (SelectedMiddleSimpleParent.parent c1 c2)) familyCard
      (fun _ _ => HigherYRegularBranch.Generic.coefficientCurve_degree _)
      Gamma (middleGammas c1 c2 d Gamma)
      (Gamma.filter fun gamma => beta.eval gamma=0)
      (LinearMessageFamily.sparseChallenges (SelectedMiddleSimpleParent.parent c1 c2) Gamma)
      (shared_roots_card beta betaNonzero betaDegree Gamma) sparseCard
    intro gamma member
    obtain ⟨inside, F, factor, higher, Q, qualified, large⟩ := Finset.mem_filter.mp member
    have root := SelectedMiddleSimpleParent.candidate_root c1 c2 d checked gamma Q
      qualified.2.1 large
    have points := qualified_points c1 c2 d checked circles west F gamma Q qualified
    rcases cover gamma ((atGamma d gamma).original Q) inside root points with
      shared | pair | sparse | fixed
    · exact Or.inl (Finset.mem_filter.mpr ⟨inside, shared⟩)
    · exact False.elim (pairRoot pair)
    · exact Or.inr (Or.inl sparse)
    · obtain ⟨messages, member, equal⟩ := fixed
      have oldRoot := qualified.2.2
      rw [equal, ← EarlyC1HigherYSupport.tupleCurve_eval] at oldRoot
      exact Or.inr (Or.inr ⟨messages, member,
        Finset.mem_filter.mpr ⟨inside, F, factor, higher, oldRoot⟩⟩)

#print axioms full_bad_partition
#print axioms high_prefix_mem
#print axioms shared_roots_card
#print axioms exists_selected_cover
end
end AspisV8.SelectedMiddleGammaCover
