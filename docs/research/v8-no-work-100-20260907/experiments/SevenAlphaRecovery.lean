import PartialFoldSelected
import ReferenceIndependentRelation
import SelectedReceivedOracle

/-! Deterministic seven-alpha recovery on a shared authenticated-word support.
Finals may depend on alpha. Four branches construct the quotient; the actual
selected line-code overlap cap identifies every branch. Seven prior zeros
then force one shared response's discrepancy polynomial to vanish.
This is not a probability root bound for the post-selected quotient, and one
tau yields only the mixed ordinary/image equation, not separate image claims. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 300000

namespace AspisV8.SevenAlphaAlgebra
open Finset Polynomial
open AspisV8.FirstImageDiscrepancy AspisV8.PostQueryFunctional
open AspisV8.ReferenceIndependentRelation AspisV8.OptimizedRelationRefinement
open AspisV8.JointImageGame
open AspisV5FriRelationCandidateBridge AspisV5ComponentCConcreteFoldLinearity
variable {K : Type*} [Field K] [DecidableEq K] [NeZero (2 : K)]

/-- Reference replacement changes no executed weight, scalar or response. -/
theorem rebase_imageWeight (pre : Before (K := K)) (Q : Fin 1024 → K) (tau : K) :
    (replaceBefore pre Q).imageWeight tau=pre.imageWeight tau := rfl

theorem rebase_snapshot_prior (pre : Before (K := K)) (Q : Fin 1024 → K)
    (tau : K) (sent : Sent K) (alpha : K) (final : Fin 256 → K) :
    ((replaceBefore pre Q).snapshot tau sent alpha).prior final=
      (pre.snapshot tau sent alpha).prior final := rfl

/-- Once independently reconstructed Q represents all seven adaptive finals,
the literal prior equations are roots of ONE degree-six polynomial. This is
finite interpolation after Q selection, not a challenge probability claim. -/
theorem seven_represented_priors (pre : Before (K := K)) (hq : pre.quarter*4=1)
    (tau : K) (sent : Sent K) (nodes : Finset K) (seven : 7≤nodes.card)
    (final : K → Fin 256 → K) (Q : Fin 1024 → K)
    (represented : ∀ alpha∈nodes, final alpha=coefficientFoldLayer 256 alpha Q)
    (zeroPrior : ∀ alpha∈nodes, (pre.snapshot tau sent alpha).prior (final alpha)=0) :
    (replaceBefore pre Q).firstError tau sent=0 ∧
      pre.claim-candidateClaim pre.ordinary Q-tau*Q 1023-
        tau^2*(pre.b*Q 1022-pre.c*Q 1021)=0 := by
  classical
  have zeros (alpha : K) (member : alpha∈nodes) :
      ((replaceBefore pre Q).firstError tau sent).eval alpha=0 := by
    rw [firstError_eval]
    change ((replaceBefore pre Q).snapshot tau sent alpha).prior
      (coefficientFoldLayer 256 alpha Q)=0
    rw [← represented alpha member,rebase_snapshot_prior]
    exact zeroPrior alpha member
  have identity : (replaceBefore pre Q).firstError tau sent=0 := by
    by_contra nonzero
    have inclusion : nodes⊆nodes.filter (fun alpha =>
        ((replaceBefore pre Q).firstError tau sent).eval alpha=0) := by
      intro alpha member
      exact Finset.mem_filter.mpr ⟨member,zeros alpha member⟩
    have roots := root_count nodes ((replaceBefore pre Q).firstError tau sent)
      nonzero 6 (firstError_degree _ _ _)
    have card := Finset.card_le_card inclusion
    omega
  refine ⟨identity,?_⟩
  have mixed := firstError_boundary (replaceBefore pre Q) hq tau sent
  rw [identity] at mixed
  simp only [boundary,Polynomial.coeff_zero,zero_add,mul_zero] at mixed
  have equation := mixed.symm
  change (imagePolynomial (pre.claim-candidateClaim pre.ordinary Q)
    (Q 1023) (pre.b*Q 1022-pre.c*Q 1021)).eval tau=0 at equation
  rw [imagePolynomial_eval] at equation
  exact equation

#print axioms rebase_imageWeight
#print axioms rebase_snapshot_prior
#print axioms seven_represented_priors
end AspisV8.SevenAlphaAlgebra

namespace AspisV8.SevenAlphaRecovery
open Finset
open AspisV8.FirstImageDiscrepancy AspisV8.PostQueryFunctional
open AspisV8.ReferenceIndependentRelation AspisV8.OptimizedRelationRefinement
open AspisV8.PartialFoldSelected
open AspisK1.V7Tag73CanonicalOneFoldSchedule
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV5ComponentCConcreteFoldLinearity AspisV5ComponentCQM31TowerExact
open AspisV5FriConcreteEncoderCommutation AspisV5FriConcreteEncoderApplicability
open AspisV5FriCoherentCandidateExtraction AspisV5FriRelationCandidateBridge
noncomputable section
local instance : NeZero (2 : QM31Exact) := AspisV8.SelectedReceivedOracle.twoNonzero

/-- Reuse the V7 canonical inverse tables and literal natural circle/line
encoder commutation. No caller-supplied source-fold identity is needed. -/
theorem selected_fold_commutes (Q : Fin 1024 → QM31Exact) (alpha : QM31Exact) :
    circleFoldLayer 262144 alpha (canonicalOneFoldSchedule 0).circleInv2x
      (canonicalOneFoldSchedule 0).circleInv2y (exactInitialEncoder Q)=
        exactFinalLinear (coefficientFoldLayer 256 alpha Q) := by
  rw [congrFun exactInitialEncoder_eq_circleLift Q]
  have inverse := canonical_one_fold_schedule_exact 0
  have h := congrArg (fun f : (Fin 1024 → QM31Exact) →ₗ[QM31Exact]
      (Fin 262144 → QM31Exact) => f Q)
    (circleFoldLayer_circleLiftEncoder exactFinalLinear alpha exactCircleX exactCircleY
      (canonicalOneFoldSchedule 0).circleInv2x
      (canonicalOneFoldSchedule 0).circleInv2y inverse.1 inverse.2)
  simpa only [LinearMap.comp_apply] using h

/-- More than 255 shared final positions identify the coefficient vector.
Received-word equality is needed only on these complete four-slot fibres. -/
theorem common_support_identifies (received : Fin 1048576 → QM31Exact)
    (S : Finset (Fin 262144)) (large : 255<S.card)
    (Q : Fin 1024 → QM31Exact)
    (recovered : ∀ i∈S, ∀ slot : Fin 4,
      exactInitialEncoder Q (childIndex i slot)=received (childIndex i slot))
    (alpha : QM31Exact) (final : Fin 256 → QM31Exact)
    (matched : ∀ i∈S, exactFinalLinear final i=circleFoldLayer 262144 alpha
      (canonicalOneFoldSchedule 0).circleInv2x
      (canonicalOneFoldSchedule 0).circleInv2y received i) :
    final=coefficientFoldLayer 256 alpha Q := by
  by_contra different
  have inclusion : S⊆agreementSet (exactFinalEncoder final)
      (exactFinalEncoder (coefficientFoldLayer 256 alpha Q)) := by
    intro i member
    have slots : (fun slot => exactInitialEncoder Q (childIndex i slot))=
        (fun slot => received (childIndex i slot)) := funext (recovered i member)
    have sameFold : circleFoldLayer 262144 alpha
          (canonicalOneFoldSchedule 0).circleInv2x
          (canonicalOneFoldSchedule 0).circleInv2y (exactInitialEncoder Q) i=
        circleFoldLayer 262144 alpha (canonicalOneFoldSchedule 0).circleInv2x
          (canonicalOneFoldSchedule 0).circleInv2y received i := by
      rw [circleFoldLayer_apply,circleFoldLayer_apply,slots]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ i,?_⟩
    exact (matched i member).trans
      (sameFold.symm.trans (congrFun (selected_fold_commutes Q alpha) i))
  have cap := exactFinalEncoder_overlap_cap final (coefficientFoldLayer 256 alpha Q) different
  have card := Finset.card_le_card inclusion
  omega

/-- Construct Q from four of the adaptive branches, not from a supplied
candidate. All seven share received R and the sufficiently large matching
support. Their actual prior zeros share the SAME compact response before
alpha. The conclusion is a deterministic single-tau mixed equation only. -/
theorem seven_alpha_common_support
    (received : Fin 1048576 → QM31Exact) (S : Finset (Fin 262144))
    (large : 255<S.card) (nodes : Finset QM31Exact) (seven : 7≤nodes.card)
    (final : QM31Exact → Fin 256 → QM31Exact)
    (pre : Before (K := QM31Exact)) (hq : pre.quarter*4=1)
    (tau : QM31Exact) (sent : Sent QM31Exact)
    (matched : ∀ alpha∈nodes, ∀ i∈S, exactFinalLinear (final alpha) i=
      circleFoldLayer 262144 alpha (canonicalOneFoldSchedule 0).circleInv2x
        (canonicalOneFoldSchedule 0).circleInv2y received i)
    (zeroPrior : ∀ alpha∈nodes, (pre.snapshot tau sent alpha).prior (final alpha)=0) :
    ∃ Q : Fin 1024 → QM31Exact,
      (∀ i∈S, ∀ slot : Fin 4,
        exactInitialEncoder Q (childIndex i slot)=received (childIndex i slot)) ∧
      (∀ alpha∈nodes, final alpha=coefficientFoldLayer 256 alpha Q) ∧
      (replaceBefore pre Q).firstError tau sent=0 ∧
      pre.claim-candidateClaim pre.ordinary Q-tau*Q 1023-
        tau^2*(pre.b*Q 1022-pre.c*Q 1021)=0 := by
  obtain ⟨fourNodes,subset,four⟩ := Finset.exists_subset_card_eq (show 4≤nodes.card by omega)
  obtain ⟨Q,recovered⟩ := four_selected_support_folds_recover received fourNodes four final
    {i | i∈S} (fun alpha member i hi => matched alpha (subset member) i hi)
  have represented : ∀ alpha∈nodes, final alpha=coefficientFoldLayer 256 alpha Q := by
    intro alpha member
    exact common_support_identifies received S large Q recovered alpha (final alpha)
      (matched alpha member)
  obtain ⟨identity,mixed⟩ := SevenAlphaAlgebra.seven_represented_priors pre hq tau sent
    nodes seven final Q represented zeroPrior
  exact ⟨Q,recovered,represented,identity,mixed⟩

#print axioms selected_fold_commutes
#print axioms common_support_identifies
#print axioms seven_alpha_common_support
end
end AspisV8.SevenAlphaRecovery
