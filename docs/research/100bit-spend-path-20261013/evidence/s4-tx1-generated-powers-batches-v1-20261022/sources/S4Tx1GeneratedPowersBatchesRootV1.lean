import S4Tx1WholeExactBatchesRootV1
import S4InstalledPrepareRawEarlyPowersV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S4Tx1GeneratedPowersBatchesRootV1
open AspisR1S4CandidateCallerPreparedRootV1
open AspisR1S4CandidatePrepareS1ParentV1
open AspisR1S4CallerStage2CarrierV1
open AspisR1S4Tx1ExactGammaBatchesRootV1
open AspisR1S4Tx1WholeExactBatchesRootV1 (installedOps)

def GeneratedPreparedBatches {H : Type}
    (sampling : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (embed : AspisR1PublicPreparation.aspis_core.field.M31 →
      Result AspisR1PublicPreparation.aspis_core.field.WideExact)
    (leaves : Leaves H) (inst : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (public1 : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice Std.U8) (hash : H)
    (obs : Option (AspisR1CurrentCaller.verifier.Phase → Result Unit))
    (aops : AspisR1Stage2.AccumulateOps) (rest : AspisR1Stage2.QueryOps) : Prop :=
  ∃ (zero : CWide) (p : CPrepared) (g : Array CWide 29#usize)
    (geometry : AspisR1CurrentCaller.verifier.QueryGeometry)
    (raw : Array AspisR1LoopPowers.field.WideExact 29#usize),
    prepareSlot
      (AspisR1ClaimPreparedBridge.concreteBoundaries
        (AspisR1ClaimPreparedBridge.InstalledMeaning.installedBoundaries sampling embed))
      leaves inst public1 proof hash obs (Array.repeat 29#usize zero) = .ok (.Ok p,g) ∧
    AspisR1LoopPowers.weights.early_powers 29#usize
      (AspisR1CurrentPreparedClaim.ClaimPowers.toPowers
        (AspisR1ClaimPreparedBridge.toClaimE
          (AspisR1S4PreparedNewS1AdapterV1.wToP p.gamma))) = .ok raw ∧
    AspisR1S4PreparedNewS1AdapterV1.wArrayFromP
      (AspisR1ClaimPreparedBridge.mapArray AspisR1ClaimPreparedBridge.fromClaimE
        (AspisR1CurrentPreparedClaim.ClaimPowers.mapArray raw)) = g ∧
    ExactTenBatches aops rest proof p g obs geometry


/-- One successful installed caller run supplies the actual generated indexed
powers result and all ten original-port batches for the same returned gamma
and scratch. Frozen source adoption and the remaining caller leaves stay open. -/
theorem accepted_tx1_generated_powers_and_batches {H : Type}
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
    k = 10#usize ∧ GeneratedPreparedBatches sampling embed leaves inst public1 proof hash obs aops rest := by
  have f0 := AspisR1S4Tx1WholeExactBatchesRootV1.accepted_tx1_exact_gamma_batches
    ops aops rest sampling embed leaves inst public1 public_bytes proof k hash obs bytes filled
  have f1 := f0 hscanBinding
  obtain ⟨hk,zero,p,g,geometry,hprep,hbatches⟩ := f1 h
  obtain ⟨raw,hraw,hmap⟩ :=
    AspisR1S4InstalledPrepareRawEarlyPowersV1.successful_prepare_exposes_generated_powers
      sampling embed leaves inst public1 proof hash obs
      (Array.repeat 29#usize zero) p g hprep
  exact ⟨hk,zero,p,g,geometry,raw,hprep,hraw,hmap,hbatches⟩

#print axioms accepted_tx1_generated_powers_and_batches
end AspisR1S4Tx1GeneratedPowersBatchesRootV1
