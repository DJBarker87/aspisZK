import S4Tx1ExactGammaBatchesRootV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S4Tx1WholeExactBatchesRootV1
open AspisR1S4CandidateCallerPreparedRootV1
open AspisR1S4CandidatePrepareS1ParentV1
open AspisR1S4CallerStage2CarrierV1
open AspisR1S4Tx1ExactGammaBatchesRootV1

def installedOps {H : Type} (ops : COps H)
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 →
      Result AspisR1PublicPreparation.aspis_core.field.WideExact)
    (leaves : Leaves H) : COps H :=
  AspisR1S4Tx1InstalledPrepareBridgeV1.withInstalledPrepare ops
    (AspisR1ClaimPreparedBridge.concreteBoundaries
      (AspisR1ClaimPreparedBridge.InstalledMeaning.installedBoundaries sampling embed)) leaves

/-- A named endpoint keeps the preparation witness and batch gamma linked
without expanding the whole query model in the caller theorem statement. -/
def PreparedBatches {H : Type}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 →
      Result AspisR1PublicPreparation.aspis_core.field.WideExact)
    (leaves : Leaves H) (inst : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (public1 : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice Std.U8) (hash : H)
    (obs : Option (AspisR1CurrentCaller.verifier.Phase → Result Unit))
    (aops : AspisR1Stage2.AccumulateOps) (rest : AspisR1Stage2.QueryOps) : Prop :=
  ∃ (zero : CWide) (p : CPrepared) (g : Array CWide 29#usize)
    (geometry : AspisR1CurrentCaller.verifier.QueryGeometry),
    prepareSlot
      (AspisR1ClaimPreparedBridge.concreteBoundaries
        (AspisR1ClaimPreparedBridge.InstalledMeaning.installedBoundaries sampling embed))
      leaves inst public1 proof hash obs (Array.repeat 29#usize zero) = .ok (.Ok p,g) ∧
    ExactTenBatches aops rest proof p g obs geometry

/-- A single successful installed source-cut tx1 supplies both the preparation
and every batch witness. Non-prepare leaves and scan binding remain explicit;
this is not frozen Std or dispatcher correspondence. -/
theorem accepted_tx1_exact_gamma_batches {H : Type}
    (ops : COps H) (aops : AspisR1Stage2.AccumulateOps) (rest : AspisR1Stage2.QueryOps)
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 →
      Result AspisR1PublicPreparation.aspis_core.field.WideExact)
    (leaves : Leaves H)
    (inst : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (public1 : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (public_bytes proof : Slice Std.U8) (k : Std.Usize) (hash : H)
    (obs : Option (AspisR1CurrentCaller.verifier.Phase → Result Unit))
    (bytes : alloc.vec.Vec Std.U8)
    (filled : Std.Usize → CQm → Result (core.result.Result (alloc.vec.Vec CQm) CCoreError))
    (hscanBinding : (installedOps ops sampling embed leaves).canonicalScan proof = .ok (.Ok ()) →
      MultiproofParserRef.parser_reference.scan proof = .ok true)
    (h : AspisR1CallerV4Tx1OpsCut.tx1
      (sourceCaller (installedOps ops sampling embed leaves) aops rest filled)
      inst public1 public_bytes proof k hash obs = .ok (.Ok bytes)) :
    k = 10#usize ∧ PreparedBatches sampling embed leaves inst public1 proof hash obs aops rest := by
  obtain ⟨hk,p,g,a,geometry,b,out,bout,hscan,⟨zero,hprep⟩,hstart,hloop⟩ :=
    source_caller_reaches_ten_loop (installedOps ops sampling embed leaves)
      aops rest inst public1 public_bytes proof k hash obs bytes filled h
  have hprep' : prepareSlot
      (AspisR1ClaimPreparedBridge.concreteBoundaries
        (AspisR1ClaimPreparedBridge.InstalledMeaning.installedBoundaries sampling embed))
      leaves inst public1 proof hash obs (Array.repeat 29#usize zero) = .ok (.Ok p,g) := hprep
  refine ⟨hk,zero,p,g,geometry,hprep',?_⟩
  have hloop' : SameCandidateLoopSuccess sampling embed leaves inst public1 proof hash obs
      zero p g aops rest a geometry b out bout := by
    change AspisR1Stage2.verifier.candidate.query_loop (candidateCall aops rest)
      proof (preparedToStage p) (accumulatorToStage a) (arrayWideToStage g)
      (obs.map (fun f => fun phase => f (phaseToCaller phase)))
      (geometryToStage geometry) (batchedWeightsToStage b) 10#usize = .ok (.Ok (out,bout))
    exact hloop
  exact same_prepare_and_loop_exact_batches sampling embed leaves inst public1 proof hash obs
    zero p g aops rest a geometry b out bout hprep' (hscanBinding hscan) hstart hloop'

#print axioms accepted_tx1_exact_gamma_batches
end AspisR1S4Tx1WholeExactBatchesRootV1
