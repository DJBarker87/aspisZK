import S4Tx1ActualGammaBridgeV1
import S4CandidateTenOriginalPortBatchesV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S4Tx1ExactGammaBatchesRootV1
open AspisR1S4CandidateCallerPreparedRootV1
open AspisR1S4PreparedNewS1AdapterV1
open AspisR1S4CandidatePrepareS1ParentV1
open AspisR1S4CallerStage2CarrierV1
open AspisR1S4FullQueryValuesPrefixV1
open AspisR1FastDotsClaimPowerCoordinateBridgeV1

def ExactTenBatches
    (aops : AspisR1Stage2.AccumulateOps) (rest : AspisR1Stage2.QueryOps)
    (proof : Slice Std.U8) (p : CPrepared) (g : Array CWide 29#usize)
    (obs : Option (AspisR1CurrentCaller.verifier.Phase → Result Unit))
    (geometry : AspisR1CurrentCaller.verifier.QueryGeometry) : Prop :=
  ∀ j : Fin 10, ∃ (a0 a1 : AspisR1Stage2.verifier.Accumulator)
    (b0 b1 : AspisR1Stage2.verifier.BatchedWeights),
    a0.next.val = j.val ∧
    AspisR1Stage2.verifier.candidate.queryWithOps aops
      (AspisR1FastDotsV10QueryOpsResultTransportV1.withOldModelDots
        AspisR1FastDotsConcreteKernelOpsRootV1.concreteOps rest)
      proof (preparedToStage p) a0 (arrayWideToStage g)
      (obs.map (fun f => fun phase => f (phaseToCaller phase)))
      (geometryToStage geometry) b0 = .ok (.Ok (a1,b1)) ∧
    AspisR1S4CandidateTenOriginalPortBatchesV1.OriginalPortBatchEvidence
      rest proof (preparedToStage p) a0 (arrayWideToStage g)
      (obs.map (fun f => fun phase => f (phaseToCaller phase)))
      (geometryToStage geometry) b0
      (AspisR1ClaimPreparedBridge.toClaimE (wToP p.gamma))

/-- The returned preparation gamma, rather than a freely existential gamma,
determines every original-port batch in this same successful ten-query loop. -/
def InstalledPrepareSuccess {H : Type}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 →
      Result AspisR1PublicPreparation.aspis_core.field.WideExact)
    (leaves : Leaves H) (inst : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (public1 : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice Std.U8) (hash : H)
    (obs : Option (AspisR1CurrentCaller.verifier.Phase → Result Unit))
    (zero : CWide) (p : CPrepared) (g : Array CWide 29#usize)
    (aops : AspisR1Stage2.AccumulateOps) (rest : AspisR1Stage2.QueryOps)
    (a : AspisR1CurrentCaller.verifier.Accumulator)
    (geometry : AspisR1CurrentCaller.verifier.QueryGeometry)
    (b : AspisR1CurrentCaller.verifier.BatchedWeights)
    (out : AspisR1Stage2.verifier.Accumulator)
    (bout : AspisR1Stage2.verifier.BatchedWeights)
 : Prop :=
  prepareSlot
      (AspisR1ClaimPreparedBridge.concreteBoundaries
        (AspisR1ClaimPreparedBridge.InstalledMeaning.installedBoundaries sampling embed))
      leaves inst public1 proof hash obs (Array.repeat 29#usize zero) = .ok (.Ok p,g)

def SameCandidateLoopSuccess {H : Type}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 →
      Result AspisR1PublicPreparation.aspis_core.field.WideExact)
    (leaves : Leaves H) (inst : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (public1 : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice Std.U8) (hash : H)
    (obs : Option (AspisR1CurrentCaller.verifier.Phase → Result Unit))
    (zero : CWide) (p : CPrepared) (g : Array CWide 29#usize)
    (aops : AspisR1Stage2.AccumulateOps) (rest : AspisR1Stage2.QueryOps)
    (a : AspisR1CurrentCaller.verifier.Accumulator)
    (geometry : AspisR1CurrentCaller.verifier.QueryGeometry)
    (b : AspisR1CurrentCaller.verifier.BatchedWeights)
    (out : AspisR1Stage2.verifier.Accumulator)
    (bout : AspisR1Stage2.verifier.BatchedWeights)
 : Prop :=
  AspisR1Stage2.verifier.candidate.query_loop (candidateCall aops rest)
      proof (preparedToStage p) (accumulatorToStage a) (arrayWideToStage g)
      (obs.map (fun f => fun phase => f (phaseToCaller phase)))
      (geometryToStage geometry) (batchedWeightsToStage b) 10#usize =
        .ok (.Ok (out,bout))

theorem same_prepare_and_loop_exact_batches {H : Type}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 →
      Result AspisR1PublicPreparation.aspis_core.field.WideExact)
    (leaves : Leaves H) (inst : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (public1 : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice Std.U8) (hash : H)
    (obs : Option (AspisR1CurrentCaller.verifier.Phase → Result Unit))
    (zero : CWide) (p : CPrepared) (g : Array CWide 29#usize)
    (aops : AspisR1Stage2.AccumulateOps) (rest : AspisR1Stage2.QueryOps)
    (a : AspisR1CurrentCaller.verifier.Accumulator)
    (geometry : AspisR1CurrentCaller.verifier.QueryGeometry)
    (b : AspisR1CurrentCaller.verifier.BatchedWeights)
    (out : AspisR1Stage2.verifier.Accumulator)
    (bout : AspisR1Stage2.verifier.BatchedWeights)
    (hprep : InstalledPrepareSuccess sampling embed leaves inst public1 proof hash obs zero p g aops rest a geometry b out bout)
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true)
    (hstart : a.next = 0#usize)
    (hloop : SameCandidateLoopSuccess sampling embed leaves inst public1 proof hash obs zero p g aops rest a geometry b out bout) :
    ExactTenBatches aops rest proof p g obs geometry := by
  obtain ⟨hgamma,hpowers,hmap⟩ :=
    AspisR1S4Tx1ActualGammaBridgeV1.actual_prepared_gamma_meaning
      sampling embed leaves inst public1 proof hash obs
      (Array.repeat 29#usize zero) g p hprep
  have hstart' : (accumulatorToStage a).next.val = 0 := by
    change a.next.val = 0
    simpa using congrArg UScalar.val hstart
  have hresult := AspisR1S4CandidateTenOriginalPortBatchesV1.candidate_ten_original_port_batches
    aops rest proof (preparedToStage p) (arrayWideToStage g)
    (obs.map (fun f => fun phase => f (phaseToCaller phase)))
    (geometryToStage geometry) (accumulatorToStage a) out
    (batchedWeightsToStage b) bout
    (AspisR1ClaimPreparedBridge.toClaimE (wToP p.gamma))
    (AspisR1ClaimPreparedBridge.mapArray AspisR1ClaimPreparedBridge.toClaimE (wArrayToP g))
    hgamma hpowers hmap hscan hstart' hloop
  exact hresult

#print axioms same_prepare_and_loop_exact_batches
end AspisR1S4Tx1ExactGammaBatchesRootV1
