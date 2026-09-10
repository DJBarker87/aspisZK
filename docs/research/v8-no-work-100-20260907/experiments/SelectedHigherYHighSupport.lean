import EarlyC1HigherYSupport
import CausalHigherYClassification

/-! Same-Q high-support refinement of the literal higher-Y prefix.
The actual final remains adaptive in alpha. Image validity is derived from
the source badAnchor gate, while the stronger support threshold is retained
as an event, not inferred from acceptance or literal-family membership.
No root count, regularity assumption, sampler law or probability product is
added by this source bridge.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.SelectedHigherYHighSupport
open Polynomial Finset
open AspisK1.V7ExactCorrelatedAgreementFactors
open AspisV5ComponentCConcreteFoldLinearity
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV8.CausalCoveredRecovery AspisV8.SelectedCoveredRelation
open AspisV8.SelectedHigherYBranch AspisV8.SelectedQuadraticReduction
open AspisV8.SelectedFactorCoherence AspisV8.SelectedOODGate
open AspisV8.GammaComponentGame AspisV8.FactorIdentityCover
open AspisV8.QuotientFamilySelected AspisV8.PartialFoldRecovery
noncomputable section
abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero
local instance decision (P : Prop) : Decidable P := Classical.propDecidable P
attribute [local irreducible] curvePrimeFactors

/-- The exact quotient-fibre threshold used by the checked helper cover.
There is no additional pole deletion or original-symbol substitution. -/
def HighSupport (received : Fin 1048576 → K) (Q : Fin 1024 → K) : Prop :=
  (fibreBad (m := 262144) (exactInitialEncoder Q) received).card ≤ 4*15334

/-- A named witness of the existing higherPrefix, with its actual final.
No choice of Q has been moved before gamma, kappa, tau or alpha. -/
def Witness {q : Nat} (e : Execution q) (gamma kappa tau alpha : K)
    (Q : Fin 1024 → K) : Prop :=
  Q ∈ literalFamily (e.raw gamma) ∧ ¬badAnchor (e.rows gamma) Q ∧
    (e.strategy gamma kappa).final tau alpha=coefficientFoldLayer 256 alpha Q ∧
    HigherCubicRoot e.c1 e.c2 e.data gamma Q

def HighPrefix {q : Nat} (e : Execution q) (gamma kappa tau alpha : K) : Prop :=
  ∃ Q, Witness e gamma kappa tau alpha Q ∧ HighSupport (e.raw gamma) Q

/-- This is the disjoint complement INSIDE higherPrefix. It says that no
representative satisfying all the same higher-prefix gates has high support. -/
def LowPrefix {q : Nat} (e : Execution q) (gamma kappa tau alpha : K) : Prop :=
  higherPrefix e gamma kappa tau alpha ∧ ¬HighPrefix e gamma kappa tau alpha

theorem witness_exists_iff {q : Nat} (e : Execution q) (gamma kappa tau alpha : K) :
    (∃ Q, Witness e gamma kappa tau alpha Q) ↔ higherPrefix e gamma kappa tau alpha :=
  Iff.rfl

/-- Actual rowPrefix/atGamma fields give the image equations directly.
The third ordinary-row gate is preserved in Witness, not needed here. -/
theorem witness_image {q : Nat} (e : Execution q) (gamma kappa tau alpha : K)
    (Q : Fin 1024 → K) (witness : Witness e gamma kappa tau alpha Q) :
    Q 1023=0 ∧ (atGamma e.data gamma).b*Q 1022-
      (atGamma e.data gamma).c*Q 1021=0 := by
  constructor
  · by_contra wrong
    exact witness.2.1 (Or.inl wrong)
  · by_contra wrong
    exact witness.2.1 (Or.inr (Or.inl wrong))

theorem high_prefix_higher {q : Nat} (e : Execution q) (gamma kappa tau alpha : K)
    (high : HighPrefix e gamma kappa tau alpha) : higherPrefix e gamma kappa tau alpha := by
  obtain ⟨Q, witness, _⟩ := high
  exact (witness_exists_iff e gamma kappa tau alpha).mp ⟨Q, witness⟩

/-- The SAME Q supplies image, high support, retained factor and root.
This inclusion is valid on both regular and singular higher branches. -/
theorem high_prefix_mem {q : Nat} (e : Execution q) (Gamma : Finset K)
    (gamma kappa tau alpha : K) (inGamma : gamma ∈ Gamma)
    (high : HighPrefix e gamma kappa tau alpha) :
    gamma ∈ EarlyC1HigherYSupport.highHigherGammas e.c1 e.c2 e.data Gamma := by
  obtain ⟨Q, witness, close⟩ := high
  have image := witness_image e gamma kappa tau alpha Q witness
  obtain ⟨F, member, retained, root, higher⟩ := witness.2.2.2
  exact Finset.mem_filter.mpr ⟨inGamma, Q, image, close,
    F, member, higher, retained, root⟩

/-- Exact event partition; unlike an existential low-support alternative,
the second branch cannot overlap the first when several Q witnesses exist. -/
theorem higher_partition {q : Nat} (e : Execution q) (gamma kappa tau alpha : K) :
    higherPrefix e gamma kappa tau alpha ↔
      HighPrefix e gamma kappa tau alpha ∨ LowPrefix e gamma kappa tau alpha := by
  constructor
  · intro selected
    by_cases high : HighPrefix e gamma kappa tau alpha
    · exact Or.inl high
    · exact Or.inr ⟨selected, high⟩
  · rintro (high | low)
    · exact high_prefix_higher e gamma kappa tau alpha high
    · exact low.1

/-- In the remaining event EVERY same-prefix witness is genuinely below
the high-support threshold; no arbitrary choice of decoder is involved. -/
theorem low_witness_bad {q : Nat} (e : Execution q) (gamma kappa tau alpha : K)
    (low : LowPrefix e gamma kappa tau alpha) (Q : Fin 1024 → K)
    (witness : Witness e gamma kappa tau alpha Q) :
    4*15334 < (fibreBad (m := 262144) (exactInitialEncoder Q) (e.raw gamma)).card := by
  apply Nat.lt_of_not_ge
  intro close
  exact low.2 ⟨Q, witness, close⟩

/-- Fixed-factor regular/singular consumers can retain their exact witness
and add the high-support test before eliminating it. Derivative information
is immaterial to this inclusion, but the actual final identity is retained. -/
theorem fixed_branch_high_prefix {q : Nat} (e : Execution q)
    (F : TrivariatePolynomial K) (factor : F ∈ curvePrimeFactors (parent e.c1 e.c2))
    (retained : Retained (point e.data)
      (fun r => CurveOODGate.answerCurve (answers e.data r)) F)
    (higher : 3 ≤ F.natDegree) (gamma kappa tau alpha : K) (Q : Fin 1024 → K)
    (qualified : Qualified e.c1 e.c2 e.data F gamma Q)
    (notBad : ¬badAnchor (e.rows gamma) Q)
    (final : (e.strategy gamma kappa).final tau alpha=coefficientFoldLayer 256 alpha Q)
    (close : HighSupport (e.raw gamma) Q) : HighPrefix e gamma kappa tau alpha :=
  ⟨Q, ⟨qualified.1, notBad, final, F, factor, retained, qualified.2.2, higher⟩, close⟩

#print axioms witness_exists_iff
#print axioms witness_image
#print axioms high_prefix_higher
#print axioms high_prefix_mem
#print axioms higher_partition
#print axioms low_witness_bad
#print axioms fixed_branch_high_prefix
end
end AspisV8.SelectedHigherYHighSupport
