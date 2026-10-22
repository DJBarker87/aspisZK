import S4Tx1ReturnedSemanticsV1
import S4Tx2TwelveReturnedLocalBatchesV1
import S4SelectedPackedReturnV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1.S4SelectedPackedTxConsumersV1

open AspisR1Stage2
open AspisV8R19.DuplexFrames
open AspisR1S4CandidateCallerPreparedRootV1
open AspisR1S4CallerStage2CarrierV1
open AspisR1S4Tx1SplitGuardRootV1
open AspisR1S4FullQueryValuesPrefixV1
open AspisR1S4TwelveQueryFieldResultsRootV1
open AspisR1FastDotsConcreteKernelOpsRootV1 (concreteOps)
open AspisR1S4Tx2FullSourceOwnedCutV1 (Ops tx2CommonFullSourceCut)
open AspisR1S4ConcreteResumeTwelveFieldsRootV2 (withConcreteResume)
open AspisR1S4FullTx2CandidateFieldsRootV1 (withS4SourceSlots)
open AspisR1S4ResumeGammaActualCanonicalV1 (withReaderE)
open AspisR1S4P6PowersQueryJoinV1 (ClaimArray sourceP6WeightsPowers stage2ToClaim)
open AspisR1FastDotsTailFieldProductRootV1 (wideDecoded)
open AspisR1.S4Tx1ReturnedSemanticsV1
open AspisR1S4Tx2TwelveReturnedLocalBatchesV1
open AspisR1.S4SelectedPackedReturnV1
open AspisR1S4QueryReturnedSemanticsV1
open AspisR1FastDotsClaimPowerCoordinateBridgeV1 (ClaimE ClaimCanonical claimArrayToFast)

private theorem local_batch_selected
    (rest : QueryOps) (proof : Slice U8) (p : verifier.Prepared)
    (a : verifier.Accumulator)
    (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (powers : Array ClaimE 29#usize) (gamma : ClaimE)
    (parsed : OraclePortCompactDraft.Parsed)
    (hlen : proof.val.length = 57607)
    (hwire : parsed.wire = MultiproofConeCanonical.bytesOf proof.val)
    (queries : Fin 22 → Fin 262144)
    (recovered0 recovered1 : Nat → Option AspisV8R19.DuplexFrames.Bytes)
    (hauth0 : ∀ pos, pos < 22 →
      recovered0 (OraclePortSelectedDraft.index queries 0 pos) =
        some (OraclePortPackedChoiceC4.payload parsed 0 pos))
    (hauth1 : ∀ pos, pos < 22 →
      recovered1 (OraclePortSelectedDraft.index queries 1 pos) =
        some (OraclePortPackedChoiceC4.payload parsed 1 pos))
    (hret : CandidateQueryReturnedLocalBatchEvidence rest proof p a g powers gamma) :
    SelectedPackedReturnEvidence rest proof p a g gamma parsed queries := by
  exact returned_values_match_selected_packed_word rest proof p a g powers gamma
    hret parsed hlen hwire queries recovered0 recovered1 hauth0 hauth1

theorem tx1_success_ten_selected_packed_batches
    {H : Type}
    (ops : COps H) (aops : AccumulateOps) (rest : QueryOps)
    (inst : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (public1 : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (public_bytes proof : Slice U8) (k : Usize) (hash : H)
    (obs : Option (AspisR1CurrentCaller.verifier.Phase → Result Unit))
    (bytes : alloc.vec.Vec U8)
    (filled : Usize → CQm → Result (core.result.Result (alloc.vec.Vec CQm) CCoreError))
    (hscanBinding : ops.canonicalScan proof = .ok (.Ok ()) →
      MultiproofParserRef.parser_reference.scan proof = .ok true)
    (hprepareBinding : ∀ (zero : CWide) (p : CPrepared) (g : Array CWide 29#usize),
      ops.prepare inst public1 proof hash obs (Array.repeat 29#usize zero) = .ok (.Ok p,g) →
      ∃ (gamma : ClaimE) (powers : Array ClaimE 29#usize),
        ClaimCanonical gamma ∧
        AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok powers ∧
        fullArrayToCurrent (arrayWideToStage g) = claimArrayToFast powers)
    (h : AspisR1CallerV4Tx1OpsCut.tx1
      (sourceCaller ops aops rest filled)
      inst public1 public_bytes proof k hash obs = .ok (.Ok bytes))
    (parsed : OraclePortCompactDraft.Parsed)
    (hlen : proof.val.length = 57607)
    (hwire : parsed.wire = MultiproofConeCanonical.bytesOf proof.val)
    (queries : Fin 22 → Fin 262144)
    (recovered0 recovered1 : Nat → Option AspisV8R19.DuplexFrames.Bytes)
    (hauth0 : ∀ pos, pos < 22 →
      recovered0 (OraclePortSelectedDraft.index queries 0 pos) =
        some (OraclePortPackedChoiceC4.payload parsed 0 pos))
    (hauth1 : ∀ pos, pos < 22 →
      recovered1 (OraclePortSelectedDraft.index queries 1 pos) =
        some (OraclePortPackedChoiceC4.payload parsed 1 pos)) :
    k = 10#usize ∧ ∃ (p : CPrepared) (g : Array CWide 29#usize)
      (geometry : AspisR1CurrentCaller.verifier.QueryGeometry)
      (gamma : ClaimE) (powers : Array ClaimE 29#usize),
      ClaimCanonical gamma ∧
      AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok powers ∧
      fullArrayToCurrent (arrayWideToStage g) = claimArrayToFast powers ∧
      ∀ i : Fin 10, ∃ (a0 a1 : verifier.Accumulator) (b0 b1 : verifier.BatchedWeights),
        a0.next.val = i.val ∧
        AspisR1S4CandidateCallerPreparedRootV1.candidateCall aops rest proof (preparedToStage p) a0 (arrayWideToStage g)
          (obs.map (fun f => fun phase => f (phaseToCaller phase)))
          (geometryToStage geometry) b0 = .ok (.Ok (a1,b1)) ∧
        SelectedPackedReturnEvidence rest proof (preparedToStage p) a0
          (arrayWideToStage g) gamma parsed queries := by
  obtain ⟨hk,p,g,geometry,gamma,powers,hgamma,hpowers,hg,hall⟩ :=
    candidate_source_tx1_success_ten_returned_local_batches
      ops aops rest inst public1 public_bytes proof k hash obs bytes filled
      hscanBinding hprepareBinding h
  refine ⟨hk,p,g,geometry,gamma,powers,hgamma,hpowers,hg,?_⟩
  intro i
  obtain ⟨a0,a1,b0,b1,hcursor,hcall,hret⟩ := hall i
  refine ⟨a0,a1,b0,b1,hcursor,hcall,?_⟩
  exact local_batch_selected rest proof (preparedToStage p) a0
    (arrayWideToStage g) powers gamma parsed hlen hwire queries recovered0 recovered1
    hauth0 hauth1 hret



theorem tx2_success_twelve_selected_packed_batches
    {H : Type}
    (ops : Ops H)
    (aops : AccumulateOps) (rest : QueryOps)
    (inst : AspisR1Stage2.aspis_core.digest.Digest32 H)
    (public_bytes proof checkpoint : Slice U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit))
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true)
    (h : tx2CommonFullSourceCut
      (withS4SourceSlots
        (withConcreteResume ops))
      (AspisR1S4FullTx2CandidateFieldsRootV1.candidateCall aops rest)
      inst public_bytes proof checkpoint hash obs = .ok (.Ok ()))
    (parsed : OraclePortCompactDraft.Parsed)
    (hlen : proof.val.length = 57607)
    (hwire : parsed.wire = MultiproofConeCanonical.bytesOf proof.val)
    (queries : Fin 22 → Fin 262144)
    (recovered0 recovered1 : Nat → Option AspisV8R19.DuplexFrames.Bytes)
    (hauth0 : ∀ pos, pos < 22 →
      recovered0 (OraclePortSelectedDraft.index queries 0 pos) =
        some (OraclePortPackedChoiceC4.payload parsed 0 pos))
    (hauth1 : ∀ pos, pos < 22 →
      recovered1 (OraclePortSelectedDraft.index queries 1 pos) =
        some (OraclePortPackedChoiceC4.payload parsed 1 pos)) :
    ∃ (p : verifier.Prepared) (a : verifier.Accumulator)
      (g : Array AspisR1Stage2.aspis_core.field.wide_exact.WideExact 29#usize)
      (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
      (powers : AspisR1S4P6PowersQueryJoinV1.ClaimArray),
      let gamma := stage2ToClaim p.gamma
      verifier.resumeWithOps
        (withReaderE ops.resumeOps)
        inst checkpoint proof public_bytes transport.Variant.S2 hash =
          .ok (.Ok (p,a)) ∧
      a.next = 10#usize ∧
      sourceP6WeightsPowers 29#usize p.gamma = .ok g ∧
      ops.forRange p.queries a.next 22#usize = .ok (.Ok geometry) ∧
      ops.newPending (alloc.vec.Vec.deref a.weights) = .ok (.Ok pending) ∧
      AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok powers ∧
      AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimCanonical gamma ∧
      AspisR1S4FullQueryValuesPrefixV1.fullArrayToCurrent g =
        AspisR1FastDotsClaimPowerCoordinateBridgeV1.claimArrayToFast powers ∧
      (∀ j : Fin 29,
        wideDecoded
          ((AspisR1S4FullQueryValuesPrefixV1.fullArrayToCurrent g).val[j.val]'(by scalar_tac)) =
          AspisR1CurrentPreparedClaim.Concrete.decode gamma ^ j.val) ∧
      (∀ k : Fin 12, ∃ (a0 a1 : verifier.Accumulator) (b0 b1 : verifier.BatchedWeights),
        a0.next.val = 10+k.val ∧
        AspisR1S4FullTx2CandidateFieldsRootV1.candidateCall aops rest proof p a0 g obs geometry b0 =
          .ok (.Ok (a1,b1)) ∧
        SelectedPackedReturnEvidence rest proof p a0 g gamma parsed queries) := by
  obtain ⟨p,a,g,geometry,pending,powers,hresume,ha,hpowers,hgeometry,hpending,
      hclaim,hmap,hsource,hreturned⟩ :=
    full_tx2_twelve_actual_returned_local_batches ops aops rest inst public_bytes proof
      checkpoint hash obs hscan h
  refine ⟨p,a,g,geometry,pending,powers,hresume,ha,hpowers,hgeometry,hpending,
    hclaim,hmap,hsource,?_⟩
  constructor
  · exact hreturned.1
  · intro k
    obtain ⟨a0,a1,b0,b1,hcursor,hcall,hret⟩ := hreturned.2 k
    refine ⟨a0,a1,b0,b1,hcursor,hcall,?_⟩
    exact local_batch_selected rest proof p a0 g powers
      (stage2ToClaim p.gamma) parsed hlen hwire queries
      recovered0 recovered1 hauth0 hauth1 hret
#print axioms tx1_success_ten_selected_packed_batches
#print axioms tx2_success_twelve_selected_packed_batches

end AspisR1.S4SelectedPackedTxConsumersV1
