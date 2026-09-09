import AspisFormal.K1.V7Tag73K13CleanCausalSource

/-! # Compiler-clean K1.3 collision set inclusion -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace AspisK1.V7Tag73K13CleanCollisionSubset

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactConcreteK13K14Events
open AspisK1.V7Tag73ExactFixedInstanceEvent
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13CleanCausalSource
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

theorem exact_clean_joint_batch_collision_subset_failure_union
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    [Fintype HiddenTape]
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {source : ExactTag73K13SourceObligations transitionFuel configuration
      projection fixedInstance decoder}
    (causal : ExactCleanCandidateDirectedK13CausalSource transitionFuel
      configuration projection fixedInstance decoder source) :
    exactFixedPlainRomLegalSameTapeEvent transitionFuel configuration projection
          fixedInstance ∩
        exactTag73K13JointQueryBatchCollisionEvent transitionFuel configuration
          projection fixedInstance decoder source ⊆
      causal.trials.failureUnion := by
  intro sample member
  rcases member with ⟨cleanMember, input, k12, ⟨collisionFacts⟩⟩
  obtain ⟨candidate, foldTrial, finalTrial, mapped⟩ :=
    causal.collisionMapped sample cleanMember input k12 collisionFacts
  apply Set.mem_iUnion.mpr
  exact ⟨candidate, Set.mem_iUnion.mpr ⟨foldTrial,
    Set.mem_iUnion.mpr ⟨finalTrial, mapped⟩⟩⟩

#print axioms exact_clean_joint_batch_collision_subset_failure_union

end
end AspisK1.V7Tag73K13CleanCollisionSubset
