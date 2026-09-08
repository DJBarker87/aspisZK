import AspisFormal.K1.V7Tag73ConcreteRootSweepClient
import AspisFormal.K1.V7Tag73ExactFixedK16Closure

/-!
# Exact K1.6 closure specialized to the deployed root-transition sweep

The generic K1.6 theorem permits an arbitrary finite restoration client.  That
is too weak a release endpoint for K1.3--K1.5: the exact locations of the
query-batch, fold and relation challenges depend on the accepted q16 trace.

This module fixes the client to `deployedRootSweepClient`.  Every round asks
for all 1513 possible root verifier-transition indices.  Non-squeeze indices
fail closed, while every actual squeeze index is requested without inspecting
its random-oracle answer or guessing its future logical role.

The theorem below changes no probability term.  It only specializes the
already checked classical-ROM compiler theorem to the concrete exhaustive
state-restoration schedule that the remaining K1.3--K1.5 proofs consume.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73ExactRootSweepK16Closure

open MeasureTheory
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ConcreteKnowledgeInsertion
open AspisK1.V7Tag73ConcreteRootSweepClient
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ExactFixedK16Closure
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedClientExtraction
open AspisK1.V7Tag73ExactOperationalResourceCertificate
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ProofRelevantUpstreamInterface
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73CanonicalFutureFreeFuel

noncomputable section

/-- Raw classical-ROM AoK bound for the concrete exhaustive root-sweep
extractor.  In particular, `configuration.client` is definitionally the
deployed 1513-transition sweep repeated `rounds` times; it is not a theorem
parameter and cannot silently be replaced by a root-only client. -/
theorem exact_root_sweep_tag73_k16_classical_rom_aok_raw
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    [Fintype HiddenTape]
    (hiddenLaw : PMF HiddenTape)
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (base : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (rounds : Nat)
    (extractor : ExactPlainRomWitnessExtractor Statement Proof Payload Witness)
    (withinForkCap : rounds * 1513 ≤ parameters.forkRequestCap)
    (projection : AcceptedTapeProjection Statement Proof Payload)
    (fixedInstance : PublicInstance Statement)
    (relation : PublicInstance Statement → Witness → Prop)
    (transitionRoom : 3 ≤ transitionFuel)
    (driverCoversProtocol :
      tag73CanonicalDriverFuelCap ≤ base.machine.driverFuel)
    (runtimeReserves : ExactOperationalRuntimeReserves parameters)
    (cutoffBeyondCap :
      totalCompilerRuntimeCap parameters < parameters.timeoutCutoff)
    (stages : ProofRelevantK12ToK15Stages transitionFuel
      (exactRootSweepWitnessConfiguration base rounds extractor withinForkCap)
      fixedInstance relation
        (ExactFixedSchedulerK12ToK15Input transitionFuel
          (exactRootSweepWitnessConfiguration base rounds extractor
            withinForkCap) projection fixedInstance))
    (terms : ConcreteUpstreamErrorTerms)
    (k12Bound : K12TwoTreeMerkle208ErrorMeasureBound hiddenLaw stages
      terms.k12TwoTreeMerkle208)
    (k13Bound : K13CircleListDecodeErrorMeasureBound hiddenLaw stages
      terms.k13CircleListDecoding)
    (k14Bound : K14CoherentChainErrorMeasureBound hiddenLaw stages
      terms.k14CoherentChainSelection)
    (k15Bound : K15SpendWitnessErrorMeasureBound hiddenLaw stages
      terms.k15SpendWitnessRecovery) :
    (exactCompilerJointLaw hiddenLaw parameters).toOuterMeasure
        (exactFixedSourceRefinementEvent transitionFuel
          (exactRootSweepWitnessConfiguration base rounds extractor
            withinForkCap) projection fixedInstance) ≤
        exactFixedPlainRomValidClientExtractionProbability hiddenLaw
          transitionFuel
          (exactRootSweepWitnessConfiguration base rounds extractor
            withinForkCap)
          fixedInstance relation +
        exactFixedClosedK16RawError terms parameters := by
  exact exact_fixed_tag73_k16_classical_rom_aok_raw
    (hiddenLaw := hiddenLaw)
    (transitionFuel := transitionFuel)
    (configuration :=
      exactRootSweepWitnessConfiguration base rounds extractor withinForkCap)
    (projection := projection)
    (fixedInstance := fixedInstance)
    (relation := relation)
    (transitionRoom := transitionRoom)
    (driverCoversProtocol := by simpa using driverCoversProtocol)
    (runtimeReserves := runtimeReserves)
    (cutoffBeyondCap := cutoffBeyondCap)
    (stages := stages)
    (terms := terms)
    (k12Bound := k12Bound)
    (k13Bound := k13Bound)
    (k14Bound := k14Bound)
    (k15Bound := k15Bound)

/-- The release configuration has the exact static request count used by the
compiler resource certificate. -/
theorem exact_root_sweep_configuration_request_count
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (base : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (rounds : Nat)
    (extractor : ExactPlainRomWitnessExtractor Statement Proof Payload Witness)
    (withinForkCap : rounds * 1513 ≤ parameters.forkRequestCap) :
    ExactRequestCount extractor (rounds * 1513)
      (exactRootSweepWitnessConfiguration base rounds extractor
        withinForkCap).client := by
  change ExactRequestCount extractor (rounds * 1513)
    (deployedRootSweepClient rounds extractor)
  exact deployed_root_sweep_client_exact_request_count rounds extractor

#print axioms exact_root_sweep_tag73_k16_classical_rom_aok_raw
#print axioms exact_root_sweep_configuration_request_count

end
end AspisK1.V7Tag73ExactRootSweepK16Closure
