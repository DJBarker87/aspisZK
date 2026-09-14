import AspisFormal.K1.V7Tag73QueryBatchChildFailure

/-!
# Source-pinned failure events for the real restored K1.3 classifier

The generic `RestoredOperationalK13FailureEvent` existentially forgets the
origin of its `words`. The event below retains the actual K1.2 return and the
actual ParsedK13 return. Universal store failure is used before choosing any
particular child. None of these predicates is silently declared predictable.
-/
set_option autoImplicit false
namespace AspisK1.V7Tag73RestoredK13ReturnedEvents
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRestoredOperationalK13Classifier
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisK1.V7Tag73RestoredDerivedK13View
open AspisK1.V7Tag73RestoredNodeK13Classifier
open AspisK1.V7Tag73StoredQueryBatchChild
open AspisK1.V7Tag73QueryBatchChildFailure
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact
noncomputable section

/-- The alternatives are exact returned computations, not just inhabited types. -/
def PinnedReturnedNodeFailure {Statement Payload : Type}
    {environment : FutureFreeEnvironment}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (node : RestoredK13Node Statement Payload)
    (data : RestoredOperationalK13Data environment node) : Prop :=
  (∃ error : RestoredNodeK12Error node,
    classifyRestoredNodeK12 node = .inr error) ∨
  ∃ k12 : RestoredNodeK12Certificate node,
    classifyRestoredNodeK12 node = .inl k12 ∧
    ∃ error : ParsedK13Error decoder k12.words (restoredOperationalK13View data),
      classifyParsedK13 decoder k12.words (restoredOperationalK13View data) = .inr error

/-- A returned K1.3 failure forces one source-pinned branch. -/
theorem returned_failure_is_pinned {Statement Payload : Type}
    {environment : FutureFreeEnvironment}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (node : RestoredK13Node Statement Payload)
    (data : RestoredOperationalK13Data environment node)
    (error : RestoredOperationalK13Error decoder node data)
    (returned : classifyRestoredOperationalK13 decoder node data = .inr error) :
    PinnedReturnedNodeFailure decoder node data := by
  unfold PinnedReturnedNodeFailure
  unfold classifyRestoredOperationalK13 at returned
  cases hk : classifyRestoredNodeK12 node with
  | inr k12Error => exact Or.inl ⟨k12Error, by simp only [hk]⟩
  | inl k12 =>
      cases hp : classifyParsedK13 decoder k12.words (restoredOperationalK13View data) with
      | inl certificate => simp [hk, hp] at returned
      | inr k13Error =>
          exact Or.inr ⟨k12, by simp only [hk], k13Error, by simp only [hp]⟩

/-- The reverse implication retains an actual total-classifier equation. -/
theorem pinned_is_returned_failure {Statement Payload : Type}
    {environment : FutureFreeEnvironment}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (node : RestoredK13Node Statement Payload)
    (data : RestoredOperationalK13Data environment node)
    (pinned : PinnedReturnedNodeFailure decoder node data) :
    ∃ error : RestoredOperationalK13Error decoder node data,
      classifyRestoredOperationalK13 decoder node data = .inr error := by
  rcases pinned with ⟨error, returned⟩ | ⟨k12, k12Returned, error, k13Returned⟩
  · exact ⟨.k12 error, by simp [classifyRestoredOperationalK13, returned]⟩
  · exact ⟨.k13 k12.words error,
      by simp [classifyRestoredOperationalK13, k12Returned, k13Returned]⟩

/-- If two actual K1.2 successes are named, their words must coincide. -/
theorem returned_k12_words_unique {Statement Payload : Type}
    {node : RestoredK13Node Statement Payload}
    (left right : RestoredNodeK12Certificate node)
    (hl : classifyRestoredNodeK12 node = .inl left)
    (hr : classifyRestoredNodeK12 node = .inl right) : left.words = right.words := by
  have same : left = right := Sum.inl.inj (hl.symm.trans hr)
  exact congrArg RestoredNodeK12Certificate.words same

variable {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
  {parameters : ExactCompilerResourceParameters} {transitionFuel : Nat}
  {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
    Observation Statement Tag73K12ParsedProof Payload Witness parameters}
  {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
  {fixedInstance : PublicInstance Statement}
  {sample : ExactCompilerSample HiddenTape parameters}
  {input : ExactK12OperationalInput transitionFuel configuration projection fixedInstance sample}
  {decoder : ExactDecoderInstantiation QM31Exact}

/-- The store's universal error pins every accepting designated child. -/
theorem failed_store_pins_child
    (failure : ExactRestoredOperationalK13Error decoder input
      (exact_restored_operational_k13_provider input))
    (child : StoredQueryBatchChild input)
    (done : child.node.verifierFinalState.current.control = .done) :
    PinnedReturnedNodeFailure decoder child.node
      ((exact_restored_operational_k13_provider input).data child.node child.member done) := by
  obtain ⟨error, returned⟩ := failure.everyDoneResult child.node child.member done
  exact returned_failure_is_pinned decoder child.node _ error returned

/-- Crucial quantifier order: all children in a designated family fail. There
is no union over stored nodes and no post-answer selector hidden in the proof. -/
theorem failed_store_pins_entire_family {Index : Type*}
    (failure : ExactRestoredOperationalK13Error decoder input
      (exact_restored_operational_k13_provider input))
    (children : Index → StoredQueryBatchChild input)
    (done : ∀ i, (children i).node.verifierFinalState.current.control = .done) :
    ∀ i, PinnedReturnedNodeFailure decoder (children i).node
      ((exact_restored_operational_k13_provider input).data
        (children i).node (children i).member (done i)) := by
  intro i
  exact failed_store_pins_child failure (children i) (done i)

/-- A family containing a genuine returned success cannot be an all-failed
store. This is independent of how many other children reject. -/
theorem one_returned_success_excludes_failed_store
    (child : StoredQueryBatchChild input)
    (done : child.node.verifierFinalState.current.control = .done)
    (certificate : RestoredOperationalK13Certificate decoder child.node
      ((exact_restored_operational_k13_provider input).data child.node child.member done))
    (returned : classifyRestoredOperationalK13 decoder child.node
      ((exact_restored_operational_k13_provider input).data child.node child.member done) =
      .inl certificate) :
    ¬ Nonempty (ExactRestoredOperationalK13Error decoder input
      (exact_restored_operational_k13_provider input)) := by
  rintro ⟨failure⟩
  exact failed_store_excludes_returned_child_success failure child done certificate returned

#print axioms returned_failure_is_pinned
#print axioms pinned_is_returned_failure
#print axioms returned_k12_words_unique
#print axioms failed_store_pins_child
#print axioms failed_store_pins_entire_family
#print axioms one_returned_success_excludes_failed_store
end
end AspisK1.V7Tag73RestoredK13ReturnedEvents
