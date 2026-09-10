import SelectedHigherYRegularTail

/-! Draft source-shaped event bridge, not an acceptance or probability
theorem. Every alternative is derived for the SAME good quotient representing
the actual post-alpha final. Fixed OOD/sparse exceptions and the original
component-tuple alternative remain explicit. A fixed-factor regular prefix
then enters the literal support-tail event with its threshold derived.
The selected-tail dependency is consumed as an already checked focused leaf.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.CausalHigherYClassification
open Polynomial Finset
open AspisV5ComponentCConcreteFoldLinearity
open AspisV8.SelectedReceivedOracle AspisV8.SelectedCoveredRelation
open AspisV8.CausalCoveredRecovery AspisV8.CausalFactorReduction
open AspisV8.SelectedQuadraticReduction AspisV8.SelectedHigherYBranch
open AspisV8.SelectedHigherYRegularTail
open AspisV8.SelectedIdentityCover AspisV8.SelectedFactorCoherence
open AspisV8.SelectedOODGate AspisV8.ComponentOODBinding
open AspisV8.EarlyC1Projection AspisV8.EarlyC1LateProjection
open AspisV8.GammaComponentGame AspisV8.OODInterpolant
open AspisV8.QuotientFamilySelected
noncomputable section
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P
attribute [local irreducible] LinearMessageFamily.family LinearMessageFamily.sparseChallenges

/-- These predicates depend only on the fixed received/OOD prefix and gamma,
not the later quotient or final selection. No probabilities are attached. -/
def exceptional {q : Nat} (e : Execution q) (Gamma : Finset K)
    (linearE quadraticE : K[X]) (quadraticBad : Finset K) (gamma : K) : Prop :=
  (∀ r, linearE.eval (point e.data r)=0) ∨
    gamma ∈ LinearMessageFamily.sparseChallenges (parent e.c1 e.c2) Gamma ∨
    (∀ r, quadraticE.eval (point e.data r)=0) ∨ gamma ∈ quadraticBad

/-- An actual original-message tuple is retained as a class, not labeled a
payment witness. The quotient/final and tuple reconstruction refer to one Q. -/
def tuplePrefix {q : Nat} (e : Execution q) (gamma kappa tau alpha : K) : Prop :=
  ∃ Q ∈ literalFamily (e.raw gamma), ¬badAnchor (e.rows gamma) Q ∧
    (e.strategy gamma kappa).final tau alpha=coefficientFoldLayer 256 alpha Q ∧
    ∃ messages ∈ LinearMessageFamily.family (parent e.c1 e.c2),
      (atGamma e.data gamma).original Q =
        ∑ j : Fin 29, gamma^j.val • messages j

theorem factor_prefix_classified {q : Nat} (e : Execution q) (Gamma : Finset K)
    (linearE quadraticE : K[X]) (quadraticBad : Finset K)
    (gamma kappa tau alpha : K)
    (cover : ∀ Q, Root e.c1 e.c2 e.data gamma Q →
      Outcome e.c1 e.c2 Gamma linearE quadraticE quadraticBad e.data gamma Q)
    (selectedPrefix : factorPrefix e gamma kappa tau alpha) :
    exceptional e Gamma linearE quadraticE quadraticBad gamma ∨
      higherPrefix e gamma kappa tau alpha ∨ tuplePrefix e gamma kappa tau alpha := by
  obtain ⟨Q, member, notBad, final, root⟩ := selectedPrefix
  rcases cover Q root with linearHit | sparse | quadraticHit | badGamma | higher | messages
  · exact Or.inl (Or.inl linearHit)
  · exact Or.inl (Or.inr (Or.inl sparse))
  · exact Or.inl (Or.inr (Or.inr (Or.inl quadraticHit)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr badGamma)))
  · exact Or.inr (Or.inl ⟨Q, member, notBad, final, higher⟩)
  · exact Or.inr (Or.inr ⟨Q, member, notBad, final, messages⟩)

/-- The actual existing algebra constructs all fixed data before OOD and
before every later strategy. No candidate-coverage premise remains here. -/
theorem exists_fixed_prefix_cover (c1 : C1Received) (c2 : C2Received)
    (Gamma : Finset K) :
    ∃ linearE quadraticE : K[X], ∃ quadraticBad : Finset K,
      linearE ≠ 0 ∧ linearE.natDegree ≤ 26854534485 ∧
      quadraticE ≠ 0 ∧ quadraticE.natDegree ≤ 114687 ∧
      quadraticBad.card ≤ 936616 ∧
      (LinearMessageFamily.family (parent c1 c2)).card ≤ 111 ∧
      (LinearMessageFamily.sparseChallenges (parent c1 c2) Gamma).card ≤ 3108 ∧
      ∀ {q : Nat} (e : Execution q), e.c1=c1 → e.c2=c2 →
      ∀ gamma kappa tau alpha, gamma ∈ Gamma →
        factorPrefix e gamma kappa tau alpha →
        exceptional e Gamma linearE quadraticE quadraticBad gamma ∨
          higherPrefix e gamma kappa tau alpha ∨ tuplePrefix e gamma kappa tau alpha := by
  obtain ⟨linearE, quadraticE, quadraticBad, linearNonzero, linearDegree,
    quadraticNonzero, quadraticDegree, badCard, familyCard, sparseCard, cover⟩ :=
      SelectedQuadraticReduction.exists_selected_reduction c1 c2 Gamma
  refine ⟨linearE, quadraticE, quadraticBad, linearNonzero, linearDegree,
    quadraticNonzero, quadraticDegree, badCard, familyCard, sparseCard, ?_⟩
  intro q e sameC1 sameC2 gamma kappa tau alpha gammaMember selectedPrefix
  subst c1
  subst c2
  exact factor_prefix_classified e Gamma linearE quadraticE quadraticBad
    gamma kappa tau alpha (fun Q root => cover e.data gamma Q gammaMember root) selectedPrefix

/-- Fixed F/row are parameters. The actual quotient may vary at all later
histories; its regularity is an event, not an assumed universal property. -/
def fixedRegularPrefix {q : Nat} (e : Execution q)
    (F : AspisK1.V7ExactCorrelatedAgreementFactors.TrivariatePolynomial K) (r : Fin 2)
    (gamma kappa tau alpha : K) : Prop :=
  ∃ Q, Qualified e.c1 e.c2 e.data F gamma Q ∧ ¬badAnchor (e.rows gamma) Q ∧
    (e.strategy gamma kappa).final tau alpha=coefficientFoldLayer 256 alpha Q ∧
    (FactorCoherence.derivativeCurve F (point e.data r)
      (CurveOODGate.answerCurve (answers e.data r))).eval gamma ≠ 0

/-- The threshold is DERIVED from this actual Q. No acceptance-conditioned
sampler, Q frozen before alpha, or supplied full-support threshold is used. -/
theorem regular_prefix_support {q : Nat} (e : Execution q)
    (checked : e.data.Checked)
    (F : AspisK1.V7ExactCorrelatedAgreementFactors.TrivariatePolynomial K) (r : Fin 2)
    (Gamma : Finset K) (gamma kappa tau alpha : K) (gammaMember : gamma ∈ Gamma)
    (selectedPrefix : fixedRegularPrefix e F r gamma kappa tau alpha) :
    gamma ∈ supportGammas e.c1 e.c2 e.data F r Gamma 38230 := by
  obtain ⟨Q, qualified, _, _, regular⟩ := selectedPrefix
  exact (mem_supportGammas e.c1 e.c2 e.data F r Gamma 38230 gamma).mpr
    ⟨gammaMember, regular, Q, qualified,
      qualified_support_38230 e.c1 e.c2 e.data checked F gamma Q qualified⟩

#print axioms factor_prefix_classified
#print axioms exists_fixed_prefix_cover
#print axioms regular_prefix_support
end
end AspisV8.CausalHigherYClassification
