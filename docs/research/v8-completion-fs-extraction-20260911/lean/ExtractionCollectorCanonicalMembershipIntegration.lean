import ExtractionCollectorVerifiedMatrix

/-!
# Canonical configuration-list membership integration

This leaf only specializes the provenance-preserving collector theorem to a
list supplied by a canonical configuration generator.  The list is kept as a
parameter: no theorem here identifies its elements with a row/column schedule
or claims that the generator emitted any particular configuration.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000
set_option maxRecDepth 1200

namespace AspisV8Completion.ExtractionCollectorCanonicalMembershipIntegration

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open ExtractionCollectorSource
open ExtractionCollectorVerifiedBodySource
open ExtractionCollectorVerifiedMatrix
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSAuthenticatedInterleavedPrefixMiddle
open FSV8V7OracleMachineBridge

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K

variable {TapeIdentity Observation Statement Proof : Type*}
variable {n m : Nat}
variable (origin : SameTapeExperimentOrigin
  TapeIdentity Observation Statement Proof Bytes)
variable (firstWork : Point → Script Bytes Block Unit n)
variable (secondWork : Point → Point → Script Bytes Block Unit m)
variable (z : Fin 10 → K) (cuts : RootCuts) (initialDigest : Block)
variable (controller : AdaptiveController) (limits : OracleLimits) (fuel : Nat)

/-- A complete matrix collected from the prefix of a canonical generated
configuration list has each selected cell's configuration in that prefix.
This is deliberately only list membership; it does not recover the generator
index, row, column, or any canonical identity theorem. -/
theorem complete_selected_configuration_mem_canonical_prefix
    (canonicalConfigurations : List OriginReplayConfiguration)
    (budget : Nat)
    (labels : MatrixLabels K K)
    (complete : CurrentComplete origin firstWork secondWork z cuts initialDigest
      controller limits fuel labels
      (verifiedAttempts origin firstWork secondWork z cuts initialDigest
        controller limits fuel canonicalConfigurations budget))
    (row : Fin 29) (column : Fin 4) :
    (complete.matrix row column).configuration ∈
      canonicalConfigurations.take budget :=
  complete_matrix_cell_configuration_mem_configurations origin firstWork
    secondWork z cuts initialDigest controller limits fuel labels
    canonicalConfigurations budget complete row column

#print axioms complete_selected_configuration_mem_canonical_prefix

end
end AspisV8Completion.ExtractionCollectorCanonicalMembershipIntegration
