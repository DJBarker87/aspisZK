import AspisFormal.K1.V7Tag73GammaRestoredK14Scope

/-!
# Exact numeric reserve for the scoped restored-gamma K1.4 prefix

The accepted verifier's block-zero gamma transition occurs before the exact
1444-step canonical driver cap.  A production root sweep reserves 1513
restoration requests.  Consequently the root plus every complete request up
to that transition still leaves substantially more than the 24 coordinates
required by the variable-prefix gamma factorization.

This file proves only that arithmetic reserve.  A separate trace lemma must
show that the literal prefix consumes no more than the stated per-request
machine/fork caps.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73GammaRestoredK14PrefixCapacity

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73CanonicalFutureFreeFuel
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73GammaRestoredK14Scope
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Machine-fresh allowance through the selected root-sweep request: the
original root plus every request up to and including the selected one. -/
def exactGammaRestoredPrefixMachineCap
    (parameters : ExactCompilerResourceParameters) (transitionIndex : Nat) : Nat :=
  parameters.q1ShaCallCap + deployedFull256VerifierCallCap +
    (transitionIndex + 1) *
      (parameters.q1ShaCallCap + deployedFull256VerifierCallCap)

/-- Fork-coordinate allowance through the selected request.  Counting its
whole pair is conservative because routing stops at the pair output. -/
def exactGammaRestoredPrefixForkCap (transitionIndex : Nat) : Nat :=
  2 * (transitionIndex + 1)

/-- The 69-request gap between the canonical 1444-step verifier and the
1513-position sweep pays for the complete 24-coordinate gamma tape, even
after charging every earlier request at its full worst-case cost. -/
theorem exact_gamma_restored_prefix_numeric_capacity
    (parameters : ExactCompilerResourceParameters)
    (transitionIndex : Nat)
    (indexWithinCanonical : transitionIndex < tag73CanonicalDriverFuelCap)
    (sweepReserved : 1513 ≤ parameters.forkRequestCap) :
    exactGammaRestoredPrefixMachineCap parameters transitionIndex +
        exactGammaRestoredPrefixForkCap transitionIndex ≤
      (exactCompilerTargetCaps parameters).length - 24 := by
  rw [exact_compiler_target_caps_length]
  apply Nat.le_sub_of_add_le
  have requestsWithPadding : transitionIndex + 1 + 12 ≤
      parameters.forkRequestCap := by
    unfold tag73CanonicalDriverFuelCap at indexWithinCanonical
    omega
  have requestCountLe : transitionIndex + 1 ≤
      parameters.forkRequestCap := by
    omega
  have machineLe := Nat.mul_le_mul_right
    (parameters.q1ShaCallCap + deployedFull256VerifierCallCap) requestCountLe
  have forkLe : 2 * (transitionIndex + 1) + 24 ≤
      2 * parameters.forkRequestCap := by
    omega
  unfold exactGammaRestoredPrefixMachineCap exactGammaRestoredPrefixForkCap
    unifiedFull256ExposureCap full256MachineFreshCap sameTapeStartCap
  omega

/-- Operational specialization for the canonical request selected from an
accepted source root. -/
theorem exact_operational_root_gamma_prefix_numeric_capacity
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (sweepReserved : 1513 ≤ parameters.forkRequestCap) :
    exactGammaRestoredPrefixMachineCap parameters
          (exactOperationalRootGammaRestorationRequest input).verifierTransitionIndex +
        exactGammaRestoredPrefixForkCap
          (exactOperationalRootGammaRestorationRequest input).verifierTransitionIndex ≤
      (exactCompilerTargetCaps parameters).length - 24 := by
  exact exact_gamma_restored_prefix_numeric_capacity parameters
    (exactOperationalRootGammaRestorationRequest input).verifierTransitionIndex
    (exact_operational_root_gamma_restoration_request_within_canonical_cap input)
    sweepReserved

#print axioms exact_gamma_restored_prefix_numeric_capacity
#print axioms exact_operational_root_gamma_prefix_numeric_capacity

end
end AspisK1.V7Tag73GammaRestoredK14PrefixCapacity
