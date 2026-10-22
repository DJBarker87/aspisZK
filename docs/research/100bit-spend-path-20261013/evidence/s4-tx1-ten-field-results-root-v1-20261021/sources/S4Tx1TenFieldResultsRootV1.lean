import S4Tx1PreparedLoopRootV1
import CallerStage2SourceConstructor
import S4Tx1SplitGuardRootV1
import S4TenNamedCallRootV1
import S4ConcreteKernelOpsRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S4Tx1TenFieldResultsRootV1
open AspisR1Stage2
open AspisR1S4CallerStage2CarrierV1
open AspisR1S4CallerStage2SourceConstructorV1
open AspisR1S4Tx1SplitGuardRootV1
open AspisR1S4FullQueryValuesPrefixV1
open AspisR1S4TwelveQueryFieldResultsRootV1
open AspisR1FastDotsConcreteKernelOpsRootV1 (concreteOps)
open AspisR1FastDotsClaimPowerCoordinateBridgeV1 (ClaimE ClaimCanonical claimArrayToFast)

attribute [local irreducible] verifier.candidate.query_loop verifier.candidate.queryWithOps

theorem generic_source_tx1_success_ten_field_results
    (headOps : AspisR1FastDotsHeadLimbForwardRootV1.Ops) {H : Type}
    (ops : COps H) (aops : AccumulateOps) (rest : QueryOps)
    (inst : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (public1 : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (public_bytes proof : Slice U8) (k : Usize) (hash : H)
    (obs : Option (AspisR1CurrentCaller.verifier.Phase → Result Unit))
    (bytes : alloc.vec.Vec U8)
    (finalLen : CVariant → Result Usize)
    (filled : Usize → CQm → Result (core.result.Result (alloc.vec.Vec CQm) CCoreError))
    (zeroQ : CQm) (zeroWide : CWide) (oneQ : CQm)
    (hscanBinding : ops.canonicalScan proof = .ok (.Ok ()) →
      MultiproofParserRef.parser_reference.scan proof = .ok true)
    (hprepareBinding : ∀ (zero : CWide) (p : CPrepared) (g : Array CWide 29#usize),
      ops.prepare inst public1 proof hash obs (Array.repeat 29#usize zero) = .ok (.Ok p,g) →
      ∃ (gamma : ClaimE) (powers : Array ClaimE 29#usize),
        ClaimCanonical gamma ∧
        AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok powers ∧
        fullArrayToCurrent (arrayWideToStage g) = claimArrayToFast powers)
    (h : AspisR1CallerV4Tx1OpsCut.tx1
      (sourceCaller ops aops rest headOps finalLen filled zeroQ zeroWide oneQ)
      inst public1 public_bytes proof k hash obs = .ok (.Ok bytes)) :
    k = 10#usize ∧ ∃ (p : CPrepared) (g : Array CWide 29#usize)
      (geometry : AspisR1CurrentCaller.verifier.QueryGeometry),
      ∀ i : Fin 10, ∃ (a0 a1 : verifier.Accumulator) (b0 b1 : verifier.BatchedWeights),
        a0.next.val = i.val ∧
        fieldCall aops rest headOps proof (preparedToStage p) a0 (arrayWideToStage g)
          (obs.map (fun f => fun phase => f (phaseToCaller phase)))
          (geometryToStage geometry) b0 = .ok (.Ok (a1,b1)) ∧
        QueryFieldEvidence headOps proof (preparedToStage p) (arrayWideToStage g) a0 := by
  obtain ⟨hk,p,g,a,geometry,b,outS,boutS,gamma,powers,hprep,hgamma,hpowers,hg,hscan,hstart,hloop⟩ :=
    source_caller_reaches_prepared_loop headOps ops aops rest inst public1 public_bytes proof k hash obs
      bytes finalLen filled zeroQ zeroWide oneQ hscanBinding hprepareBinding h
  have hs : (accumulatorToStage a).next.val = 0 := by
    change a.next.val = 0
    rw [hstart]
    rfl
  have hf : fieldCall aops rest headOps = AspisR1S4TenNamedCallRootV1.namedCall aops headOps rest := rfl
  have hloopNamed := Eq.mp (congrArg (fun call : QueryCall =>
    verifier.candidate.query_loop call proof (preparedToStage p) (accumulatorToStage a)
      (arrayWideToStage g) (obs.map (fun f => fun phase => f (phaseToCaller phase)))
      (geometryToStage geometry) (batchedWeightsToStage b) 10#usize = .ok (.Ok (outS,boutS))) hf) hloop
  trace "named call ready"
  have all := AspisR1S4TenNamedCallRootV1.ten_named_call_field_results
    aops headOps rest proof (preparedToStage p) (arrayWideToStage g)
    (obs.map (fun f => fun phase => f (phaseToCaller phase)))
    (geometryToStage geometry) (accumulatorToStage a) outS (batchedWeightsToStage b) boutS
    gamma powers hgamma hpowers hg hscan hs hloopNamed
  trace "ten result ready"
  refine ⟨hk,p,g,geometry,?_⟩
  simpa only [fieldCall, AspisR1S4TenNamedCallRootV1.namedCall] using all

/-- Closed arithmetic backend specialization. Remaining caller/scanner/preparation
source interfaces are those in the generic statement; no field operation law
or independent query-loop success is added. -/
abbrev source_tx1_success_ten_field_results :=
  @generic_source_tx1_success_ten_field_results concreteOps

#print axioms source_caller_reaches_ten_loop
#print axioms generic_source_tx1_success_ten_field_results
#print axioms source_tx1_success_ten_field_results
end AspisR1S4Tx1TenFieldResultsRootV1
