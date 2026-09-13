import AspisFormal.K1.V7Tag73StoredQueryBatchChild

/-!
# Honest child dispositions for restoration-wide K1.3 failure

A stored child can reject. A request need not insert a child. Neither outcome
is a degree-sixteen collision. This module keeps these outcomes visible and
retains the exact error returned by the real node classifier.

The resulting event inclusion is deterministic. The existential events here
are NOT declared predictable targets, and their measures are not claimed small.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73QueryBatchChildFailure

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRestoredOperationalK13Classifier
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73RestoredDerivedK13View
open AspisK1.V7Tag73StoredQueryBatchChild
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

variable {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
  {parameters : ExactCompilerResourceParameters}
  {transitionFuel : Nat}
  {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
    Observation Statement Tag73K12ParsedProof Payload Witness parameters}
  {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
  {fixedInstance : PublicInstance Statement}

/-- Successful execution, failed *returned* classification, on this child. -/
def ChildReturnedFailure
    {sample : ExactCompilerSample HiddenTape parameters}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (child : StoredQueryBatchChild input) : Prop :=
  ∃ done : child.node.verifierFinalState.current.control = .done,
    ∃ error : RestoredOperationalK13Error decoder child.node
      ((exact_restored_operational_k13_provider input).data child.node child.member done),
      classifyRestoredOperationalK13 decoder child.node
        ((exact_restored_operational_k13_provider input).data child.node child.member done) =
          .inr error

/-- Universal failure applies to the same canonical child, without replacing
it by the root or forgetting the classifier equation. -/
theorem failed_store_failed_done_child
    {sample : ExactCompilerSample HiddenTape parameters}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (failure : ExactRestoredOperationalK13Error decoder input
      (exact_restored_operational_k13_provider input))
    (child : StoredQueryBatchChild input)
    (done : child.node.verifierFinalState.current.control = .done) :
    ChildReturnedFailure decoder child := by
  obtain ⟨error, returned⟩ := failure.everyDoneResult child.node child.member done
  exact ⟨done, error, returned⟩

/-- All canonical children, not an answer-dependent chosen subset, satisfy
this disjunction on the failed store. -/
theorem failed_store_child_disposition
    {sample : ExactCompilerSample HiddenTape parameters}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (failure : ExactRestoredOperationalK13Error decoder input
      (exact_restored_operational_k13_provider input))
    (child : StoredQueryBatchChild input) :
    child.node.verifierFinalState.current.control ≠ .done ∨
      ChildReturnedFailure decoder child := by
  classical
  by_cases done : child.node.verifierFinalState.current.control = .done
  · exact Or.inr (failed_store_failed_done_child failure child done)
  · exact Or.inl done

/-- A genuine returned child success contradicts universal failure. Inhabiting
a certificate type without a returned equation is not used for this step. -/
theorem failed_store_excludes_returned_child_success
    {sample : ExactCompilerSample HiddenTape parameters}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (failure : ExactRestoredOperationalK13Error decoder input
      (exact_restored_operational_k13_provider input))
    (child : StoredQueryBatchChild input)
    (done : child.node.verifierFinalState.current.control = .done)
    (success : RestoredOperationalK13Certificate decoder child.node
      ((exact_restored_operational_k13_provider input).data child.node child.member done))
    (returned : classifyRestoredOperationalK13 decoder child.node
      ((exact_restored_operational_k13_provider input).data child.node child.member done) =
        .inl success) : False := by
  have failed := (failure.everyDoneResult child.node child.member done).2
  rw [returned] at failed
  cases failed

/-- Canonical request with no retained child: includes execution/preparation
failure, not just a failed field sample. The source proof must refine this. -/
def MissingQueryBatchChildEvent
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃ input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample, ¬ Nonempty (StoredQueryBatchChild input)}

/-- Normally returned nonaccepting child. Its mass must not be erased. -/
def RejectedQueryBatchChildEvent
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃ (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) (child : StoredQueryBatchChild input),
      child.node.verifierFinalState.current.control ≠ .done}

/-- Same-law event for a canonical child and its actual returned error. -/
def FailedQueryBatchChildEvent
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) :
    Set (ExactCompilerSample HiddenTape parameters) :=
  {sample | ∃ (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) (child : StoredQueryBatchChild input),
      ChildReturnedFailure decoder child}

/-- No missing/return-rejection branch is silently called a rare collision. -/
theorem restored_failure_subset_child_dispositions
    (decoder : ExactDecoderInstantiation QM31Exact) :
    exactTag73RestoredOperationalK13FailureEvent transitionFuel configuration
        projection fixedInstance decoder ⊆
      MissingQueryBatchChildEvent transitionFuel configuration projection fixedInstance ∪
      (RejectedQueryBatchChildEvent transitionFuel configuration projection fixedInstance ∪
        FailedQueryBatchChildEvent transitionFuel configuration projection fixedInstance decoder) := by
  classical
  rintro sample ⟨input, ⟨failure⟩⟩
  by_cases present : Nonempty (StoredQueryBatchChild input)
  · obtain ⟨child⟩ := present
    rcases failed_store_child_disposition failure child with rejected | failed
    · exact Or.inr (Or.inl ⟨input, child, rejected⟩)
    · exact Or.inr (Or.inr ⟨input, child, failed⟩)
  · exact Or.inl ⟨input, present⟩

/-- An exact same-measure inequality. This is an accounting diagnostic, not a
closed security bound: all three RHS measures remain actual quantities. -/
theorem restored_failure_measure_le_child_dispositions
    [Fintype HiddenTape] (hiddenLaw : PMF HiddenTape)
    (clean : Set (ExactCompilerSample HiddenTape parameters))
    (decoder : ExactDecoderInstantiation QM31Exact) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩ exactTag73RestoredOperationalK13FailureEvent transitionFuel
          configuration projection fixedInstance decoder) ≤
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩ MissingQueryBatchChildEvent transitionFuel configuration projection fixedInstance) +
      ((exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩ RejectedQueryBatchChildEvent transitionFuel configuration projection fixedInstance) +
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩ FailedQueryBatchChildEvent transitionFuel configuration projection fixedInstance decoder)) := by
  let μ := (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
  have inclusion := restored_failure_subset_child_dispositions
    (transitionFuel := transitionFuel) (configuration := configuration)
    (projection := projection) (fixedInstance := fixedInstance) decoder
  have restricted : clean ∩ exactTag73RestoredOperationalK13FailureEvent
        transitionFuel configuration projection fixedInstance decoder ⊆
      (clean ∩ MissingQueryBatchChildEvent transitionFuel configuration projection fixedInstance) ∪
      ((clean ∩ RejectedQueryBatchChildEvent transitionFuel configuration projection fixedInstance) ∪
       (clean ∩ FailedQueryBatchChildEvent transitionFuel configuration projection fixedInstance decoder)) := by
    rintro s ⟨hs, hf⟩
    rcases inclusion hf with missing | rejected | failed
    · exact Or.inl ⟨hs, missing⟩
    · exact Or.inr (Or.inl ⟨hs, rejected⟩)
    · exact Or.inr (Or.inr ⟨hs, failed⟩)
  exact (μ.mono restricted).trans
    ((measure_union_le _ _).trans
      (add_le_add le_rfl (measure_union_le _ _)))

#print axioms failed_store_failed_done_child
#print axioms failed_store_child_disposition
#print axioms failed_store_excludes_returned_child_success
#print axioms restored_failure_subset_child_dispositions
#print axioms restored_failure_measure_le_child_dispositions

end
end AspisK1.V7Tag73QueryBatchChildFailure
