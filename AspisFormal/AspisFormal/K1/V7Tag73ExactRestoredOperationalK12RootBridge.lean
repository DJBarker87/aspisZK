import AspisFormal.K1.V7Tag73ExactConcreteK12Bound
import AspisFormal.K1.V7Tag73ExactRestoredOperationalK13Events

/-!
# Root K1.2 authentication bridge for restoration-wide Tag-73

The restoration-wide K1.3 classifier includes an authentication failure for
every stored node.  At the literal accepted root that predicate is definitionally
the fixed K1.2 opening predicate.  The ordinary checked-source K1.2 obligation
therefore eliminates the root authentication branch; it is not a separate
probabilistic loss.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73ExactRestoredOperationalK12RootBridge

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactConcreteK12Bound
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactRestoredOperationalK13Events
open AspisK1.V7Tag73ExactRestoredOperationalK13Classifier
open AspisK1.V7Tag73RestoredNodeK13Classifier
open AspisPool.V7MerkleQueryExtractor

/-- At the literal accepted root, restoration-wide authentication failure is
impossible once the checked production source has accepted the paired openings.
This theorem is purely deterministic; the 208-bit extraction/collision term is
still accounted for separately. -/
theorem exact_restored_operational_root_k12_authentication_event_eq_empty
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    (source : ExactTag73K12SourceObligations transitionFuel configuration
      projection fixedInstance) :
    exactTag73RestoredOperationalRootK12AuthenticationEvent transitionFuel
        configuration projection fixedInstance = ∅ := by
  ext sample
  constructor
  · rintro ⟨input, rejected⟩
    apply False.elim
    apply rejected
    simpa [exactTag73RestoredOperationalRootK12AuthenticationEvent,
      exactTag73RestoredOperationalK13RootEvent, restoredNodeK12Truncate,
      restoredNodeK12Roots, restoredNodeK12Openings, exactK12Truncate,
      exactK12Roots, exactK12Openings] using source.openingsAccepted sample input
  · simp

/-- Consequently the K1.3 measured composition needs a source/probability
bound only for root extraction failure, not for a spurious union containing
authentication failure. -/
theorem exact_restored_operational_root_k12_union_bound_of_extraction_bound
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    (source : ExactTag73K12SourceObligations transitionFuel configuration
      projection fixedInstance)
    (clean : Set (ExactCompilerSample HiddenTape parameters))
    {bound : ENNReal}
    (extractionBound :
      (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
          (clean ∩ exactTag73RestoredOperationalRootK12ExtractionEvent
            transitionFuel configuration projection fixedInstance) ≤ bound) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (clean ∩
          (exactTag73RestoredOperationalRootK12AuthenticationEvent
              transitionFuel configuration projection fixedInstance ∪
            exactTag73RestoredOperationalRootK12ExtractionEvent
              transitionFuel configuration projection fixedInstance)) ≤ bound := by
  rw [exact_restored_operational_root_k12_authentication_event_eq_empty source]
  simpa using extractionBound

#print axioms exact_restored_operational_root_k12_authentication_event_eq_empty
#print axioms exact_restored_operational_root_k12_union_bound_of_extraction_bound

end AspisK1.V7Tag73ExactRestoredOperationalK12RootBridge
