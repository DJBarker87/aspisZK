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

abbrev COps := AspisR1CallerV4Tx1OpsCut.Ops
abbrev CPrepared := AspisR1CurrentCaller.verifier.Prepared
abbrev CWide := AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact
abbrev CQm := AspisR1CurrentCaller.aspis_core.field.QM31
abbrev CVariant := AspisR1CurrentCaller.transport.Variant
abbrev CCoreError := AspisR1CurrentCaller.aspis_core.r0.Error

def fieldCall (aops : AccumulateOps) (rest : QueryOps) (headOps : AspisR1FastDotsHeadLimbForwardRootV1.Ops) : QueryCall :=
  AspisR1S4TenNamedCallRootV1.namedCall aops headOps rest

def sourceCaller {H : Type} (ops : COps H) (aops : AccumulateOps) (rest : QueryOps)
    (headOps : AspisR1FastDotsHeadLimbForwardRootV1.Ops)
    (finalLen : CVariant → Result Usize)
    (filled : Usize → CQm → Result (core.result.Result (alloc.vec.Vec CQm) CCoreError))
    (zeroQ : CQm) (zeroWide : CWide) (oneQ : CQm) : COps H :=
  { withSourceAccumulatorNew ops finalLen filled zeroQ zeroWide oneQ with
    split := 10#usize
    queryLoop := stage2QueryLoopAdapter (fieldCall aops rest headOps) }

/-- Upstream preparation and scanner refinements are explicit. The ten successful
query calls, zero starting cursor and split=10 are derived from one caller run,
not independently assumed. The closed specialization below supplies the
complete concrete S4 arithmetic record. Frozen Rust child/library installation remains outside this theorem. -/
theorem source_caller_reaches_ten_loop
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
    (h : AspisR1CallerV4Tx1OpsCut.tx1
      (sourceCaller ops aops rest headOps finalLen filled zeroQ zeroWide oneQ)
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
      verifier.candidate.query_loop (fieldCall aops rest headOps) proof (preparedToStage p)
        (accumulatorToStage a) (arrayWideToStage g)
        (obs.map (fun f => fun phase => f (phaseToCaller phase)))
        (geometryToStage geometry) (batchedWeightsToStage b) 10#usize = .ok (.Ok (outS,boutS)) := by
  have hk : k = 10#usize :=
    tx1_success_requires_split (sourceCaller ops aops rest headOps finalLen filled zeroQ zeroWide oneQ)
      inst public1 public_bytes proof k hash obs bytes h
  have h' : AspisR1CallerV4Tx1OpsCut.tx1
      { withSourceAccumulatorNew (withFrozenSplit ops) finalLen filled zeroQ zeroWide oneQ with
        queryLoop := stage2QueryLoopAdapter (fieldCall aops rest headOps) }
      inst public1 public_bytes proof k hash obs = .ok (.Ok bytes) := h
  obtain ⟨parsed,zero,p,g,a,geometry,b,out,bout,outS,boutS,
    hparse,hscan,hzero,hprep,hloop,hnew,hout,hbout,hstart⟩ :=
    tx1_source_constructor_success_starts_zero (withFrozenSplit ops) (fieldCall aops rest headOps)
      inst public1 public_bytes proof k hash obs bytes finalLen filled zeroQ zeroWide oneQ h'
  refine ⟨hk,p,g,a,geometry,b,outS,boutS,hscan,⟨zero,hprep⟩,hstart,?_⟩
  simpa only [hk] using hloop


#print axioms source_caller_reaches_ten_loop
end AspisR1S4Tx1TenFieldResultsRootV1
