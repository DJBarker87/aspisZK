import CallerStage2SourceConstructor
import S4Tx1SplitGuardRootV1
import S4TenQueryFieldResultsRootV1
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

abbrev COps := AspisR1CallerV4Tx1OpsCut.Ops
abbrev CPrepared := AspisR1CurrentCaller.verifier.Prepared
abbrev CWide := AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact
abbrev CQm := AspisR1CurrentCaller.aspis_core.field.QM31
abbrev CVariant := AspisR1CurrentCaller.transport.Variant
abbrev CCoreError := AspisR1CurrentCaller.aspis_core.r0.Error

def fieldCall (aops : AccumulateOps) (rest : QueryOps) : QueryCall :=
  fun proof p a g obs geometry b => verifier.candidate.queryWithOps aops
    (withS4Callbacks (AspisR1FastDotsFourCallbacksForwardRootV1.install concreteOps) rest)
    proof p a g obs geometry b

def sourceCaller {H : Type} (ops : COps H) (aops : AccumulateOps) (rest : QueryOps)
    (finalLen : CVariant → Result Usize)
    (filled : Usize → CQm → Result (core.result.Result (alloc.vec.Vec CQm) CCoreError))
    (zeroQ : CQm) (zeroWide : CWide) (oneQ : CQm) : COps H :=
  { withSourceAccumulatorNew ops finalLen filled zeroQ zeroWide oneQ with
    split := 10#usize
    queryLoop := stage2QueryLoopAdapter (fieldCall aops rest) }

/-- Upstream preparation and scanner refinements are explicit. The ten successful
query calls, zero starting cursor and split=10 are derived from one caller run,
not independently assumed. Arithmetic operations are the complete concrete S4
record. Frozen Rust child/library installation remains outside this theorem. -/
theorem source_tx1_success_ten_field_results {H : Type}
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
      (sourceCaller ops aops rest finalLen filled zeroQ zeroWide oneQ)
      inst public1 public_bytes proof k hash obs = .ok (.Ok bytes)) :
    k = 10#usize ∧ ∃ (p : CPrepared) (g : Array CWide 29#usize)
      (geometry : AspisR1CurrentCaller.verifier.QueryGeometry),
      ∀ i : Fin 10, ∃ (a0 a1 : verifier.Accumulator) (b0 b1 : verifier.BatchedWeights),
        a0.next.val = i.val ∧
        fieldCall aops rest proof (preparedToStage p) a0 (arrayWideToStage g)
          (obs.map (fun f => fun phase => f (phaseToCaller phase)))
          (geometryToStage geometry) b0 = .ok (.Ok (a1,b1)) ∧
        QueryFieldEvidence concreteOps proof (preparedToStage p) (arrayWideToStage g) a0 := by
  trace "before split"
  have hk : k = 10#usize :=
    tx1_success_requires_split (sourceCaller ops aops rest finalLen filled zeroQ zeroWide oneQ)
      inst public1 public_bytes proof k hash obs bytes h
  trace "before caller adapter"
  have h' : AspisR1CallerV4Tx1OpsCut.tx1
      { withSourceAccumulatorNew (withFrozenSplit ops) finalLen filled zeroQ zeroWide oneQ with
        queryLoop := stage2QueryLoopAdapter (fieldCall aops rest) }
      inst public1 public_bytes proof k hash obs = .ok (.Ok bytes) := h
  trace "before caller theorem"
  obtain ⟨parsed,zero,p,g,a,geometry,b,out,bout,outS,boutS,
    hparse,hscan,hzero,hprep,hloop,hnew,hout,hbout,hstart⟩ :=
    tx1_source_constructor_success_starts_zero (withFrozenSplit ops) (fieldCall aops rest)
      inst public1 public_bytes proof k hash obs bytes finalLen filled zeroQ zeroWide oneQ h'
  trace "before prep"
  obtain ⟨gamma,powers,hgamma,hpowers,hg⟩ := hprepareBinding zero p g hprep
  trace "before cursor"
  have hs : (accumulatorToStage a).next.val = 0 := by
    change a.next.val = 0
    rw [hstart]
    rfl
  trace "before loop end"
  rw [hk] at hloop
  trace "before ten theorem"
  have all := AspisR1S4TenQueryFieldResultsRootV1.ten_queries_have_field_results
    aops concreteOps rest proof (preparedToStage p) (arrayWideToStage g)
    (obs.map (fun f => fun phase => f (phaseToCaller phase)))
    (geometryToStage geometry) (accumulatorToStage a) outS (batchedWeightsToStage b) boutS
    gamma powers hgamma hpowers hg (hscanBinding hscan) hs hloop
  trace "before final"
  exact ⟨hk,p,g,geometry,all⟩

#print axioms source_tx1_success_ten_field_results
end AspisR1S4Tx1TenFieldResultsRootV1
