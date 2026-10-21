import AspisR1AccumulatorNewConcreteChildrenV4
import S4Tx1SplitGuardRootV1
import S4V10ConcreteQueryOpsBuilderV1
import S4ConcreteKernelOpsRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S4CandidateCallerPreparedRootV1
open AspisR1FastDotsV10ConcreteQueryOpsBuilderV1
open AspisR1Stage2
open AspisR1S4CallerStage2CarrierV1
open AspisR1S4AccumulatorNewConcreteChildrenV4
open AspisR1S4Tx1SplitGuardRootV1
open AspisR1S4FullQueryValuesPrefixV1
open AspisR1S4TwelveQueryFieldResultsRootV1
open AspisR1FastDotsConcreteKernelOpsRootV1 (concreteOps)
open AspisR1FastDotsClaimPowerCoordinateBridgeV1 (ClaimE ClaimCanonical claimArrayToFast)

abbrev COps := AspisR1CallerV4Tx1OpsCut.Ops
abbrev CPrepared := AspisR1CurrentCaller.verifier.Prepared
abbrev CWide := AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact
abbrev CQm := AspisR1CurrentCaller.aspis_core.field.QM31
abbrev CVariant := AspisR1CurrentCaller.transport.Variant
abbrev CCoreError := AspisR1CurrentCaller.aspis_core.r0.Error

def candidateCall (aops : AccumulateOps) (rest : QueryOps) : QueryCall :=
  verifier.candidate.queryWithOps aops (concreteCandidateQueryOps rest)

def sourceCaller {H : Type} (ops : COps H) (aops : AccumulateOps) (rest : QueryOps)
    (filled : Usize → CQm → Result (core.result.Result (alloc.vec.Vec CQm) CCoreError)) : COps H :=
  { withConcreteConstructorChildren ops filled with
    split := 10#usize
    queryLoop := stage2QueryLoopAdapter (candidateCall aops rest) }

/-- Upstream preparation and scanner refinements are explicit. The ten successful
query calls, zero starting cursor and split=10 are derived from one caller run,
not independently assumed. The closed specialization below supplies the
complete concrete S4 arithmetic record. Frozen Rust child/library installation remains outside this theorem. -/
theorem source_caller_reaches_ten_loop
    {H : Type}
    (ops : COps H) (aops : AccumulateOps) (rest : QueryOps)
    (inst : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (public1 : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (public_bytes proof : Slice U8) (k : Usize) (hash : H)
    (obs : Option (AspisR1CurrentCaller.verifier.Phase → Result Unit))
    (bytes : alloc.vec.Vec U8)
    (filled : Usize → CQm → Result (core.result.Result (alloc.vec.Vec CQm) CCoreError))
    (h : AspisR1CallerV4Tx1OpsCut.tx1
      (sourceCaller ops aops rest filled)
      inst public1 public_bytes proof k hash obs = .ok (.Ok bytes)) :
    k = 10#usize ∧ ∃ (p : CPrepared) (g : Array CWide 29#usize)
      (a : AspisR1CurrentCaller.verifier.Accumulator)
      (geometry : AspisR1CurrentCaller.verifier.QueryGeometry)
      (b : AspisR1CurrentCaller.verifier.BatchedWeights)
      (outS : verifier.Accumulator) (boutS : verifier.BatchedWeights),
      ops.canonicalScan proof = .ok (.Ok ()) ∧
      (∃ zero : CWide, ops.prepare inst public1 proof hash obs
        (Array.repeat 29#usize zero) = .ok (.Ok p,g)) ∧
      a.next = 0#usize ∧
      verifier.candidate.query_loop (candidateCall aops rest) proof (preparedToStage p)
        (accumulatorToStage a) (arrayWideToStage g)
        (obs.map (fun f => fun phase => f (phaseToCaller phase)))
        (geometryToStage geometry) (batchedWeightsToStage b) 10#usize = .ok (.Ok (outS,boutS)) := by
  have hk : k = 10#usize :=
    tx1_success_requires_split (sourceCaller ops aops rest filled)
      inst public1 public_bytes proof k hash obs bytes h
  have h' : AspisR1CallerV4Tx1OpsCut.tx1
      { withConcreteConstructorChildren (withFrozenSplit ops) filled with
        queryLoop := stage2QueryLoopAdapter (candidateCall aops rest) }
      inst public1 public_bytes proof k hash obs = .ok (.Ok bytes) := h
  obtain ⟨parsed,zero,p,g,a,geometry,b,out,bout,outS,boutS,
    hparse,hscan,hzero,hprep,hloop,hnew,hout,hbout,hstart⟩ :=
    tx1_success_same_query_initial_next_zero (withFrozenSplit ops)
      (candidateCall aops rest) inst public1 public_bytes proof k hash obs bytes filled h' 
  refine ⟨hk,p,g,a,geometry,b,outS,boutS,hscan,⟨zero,hprep⟩,hstart,?_⟩
  simpa only [hk] using hloop


theorem source_caller_reaches_prepared_loop
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
      inst public1 public_bytes proof k hash obs = .ok (.Ok bytes)) :
    k = 10#usize ∧ ∃ (p : CPrepared) (g : Array CWide 29#usize)
      (a : AspisR1CurrentCaller.verifier.Accumulator)
      (geometry : AspisR1CurrentCaller.verifier.QueryGeometry)
      (b : AspisR1CurrentCaller.verifier.BatchedWeights)
      (outS : verifier.Accumulator) (boutS : verifier.BatchedWeights)
      (gamma : ClaimE) (powers : Array ClaimE 29#usize),
      (∃ zero : CWide, ops.prepare inst public1 proof hash obs
        (Array.repeat 29#usize zero) = .ok (.Ok p,g)) ∧
      ClaimCanonical gamma ∧
      AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok powers ∧
      fullArrayToCurrent (arrayWideToStage g) = claimArrayToFast powers ∧
      MultiproofParserRef.parser_reference.scan proof = .ok true ∧
      a.next = 0#usize ∧
      verifier.candidate.query_loop (candidateCall aops rest) proof (preparedToStage p)
        (accumulatorToStage a) (arrayWideToStage g)
        (obs.map (fun f => fun phase => f (phaseToCaller phase)))
        (geometryToStage geometry) (batchedWeightsToStage b) 10#usize = .ok (.Ok (outS,boutS)) := by
  obtain ⟨hk,p,g,a,geometry,b,outS,boutS,hscan,⟨zero,hprep⟩,hstart,hloop⟩ :=
    source_caller_reaches_ten_loop ops aops rest inst public1 public_bytes proof k hash obs
      bytes filled h
  obtain ⟨gamma,powers,hgamma,hpowers,hg⟩ := hprepareBinding zero p g hprep
  exact ⟨hk,p,g,a,geometry,b,outS,boutS,gamma,powers,⟨zero,hprep⟩,
    hgamma,hpowers,hg,hscanBinding hscan,hstart,hloop⟩


#print axioms source_caller_reaches_ten_loop
#print axioms source_caller_reaches_prepared_loop
end AspisR1S4CandidateCallerPreparedRootV1
