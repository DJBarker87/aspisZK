import R1Z.PV_RunJoin_NativeMergeValue73
import R1Z.PV_RunJoin_NativeInterpolationBoundary73
import R1Z.PV_RunJoin_InterpolationCells73
import R1Z.PV_RunJoin_NativeRoundTail73
import R1Z.PV_RunJoin_RoundWorkerPlan69
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeWorkerRound73
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
open PV_RunJoin_FieldData34 (value canonical)
open PV_RunJoin_SampleDomain34 (count assignments remaining)
open scoped BigOperators
abbrev Q := aspis_core.field.QM31
abbrev T := host_wire.SemanticTranscript aspis_core.digest.LegacyHashFn
variable {S F O : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)

theorem complete (oi : host_sumcheck.Oracle O) (oracle : O)
    (t : T) (output : alloc.vec.Vec U8) (point : Array Q 10#usize) (running : Q)
    (round : Usize) (bound : round.val<10)
    (evaluations : alloc.vec.Vec (core.result.Result Q r1_wire.Error)) (es : Nat → Q)
    (worker : letI : ExternalTypes := types base
      letI : ExternalFuns := opsNative base heap box ops runtime world
      @host_work.map (types base) ops _ _
        (host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnTupleUsizeResultQM31Error
          aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 oi)
        (Usize.wrapping_add 100#usize round) (count round)
        (oracle,point,round,assignments round)=ok evaluations)
    (size : evaluations.length=(count round).val)
    (agrees : ∀ i : Usize,i.val<(count round).val →
      Slice.index_usize (alloc.vec.Vec.deref evaluations) i=ok (.Ok (es i.val)))
    (canon : ∀ j,j<(count round).val → canonical (es j))
    (hclaim : canonical running)
    (sum : value running=
      (∑ j ∈ Finset.range (count round).val,if j/(assignments round).val=0 then value (es j) else 0)+
      (∑ j ∈ Finset.range (count round).val,if j/(assignments round).val=1 then value (es j) else 0))
    (order : PV_RunJoin_RoundRow73.row round=t.next_row)
    (total : ∀ parts,∃ b,t.hash parts=ok b)
    (outputSize : output.length=171+901*round.val) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops runtime world
    ∃ point' running' next after,
      host_sumcheck.prove_sumcheck_round aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
        oi t output point running round oracle=ok (.Ok (point',running'),next,after) ∧
      next.next_row.val=16+round.val ∧ next.hash=t.hash ∧ after.length=171+901*(round.val+1) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  obtain ⟨values,merged,hcan,hvalue⟩ := PV_RunJoin_NativeMergeValue73.complete
    base heap box ops runtime world round bound es (alloc.vec.Vec.deref evaluations) size agrees canon
  have sumCells : value running=
      value (PV_RunJoin_InterpolationInput72.cells (PV_RunJoin_MergeArray35.array values) 0)+
      value (PV_RunJoin_InterpolationInput72.cells (PV_RunJoin_MergeArray35.array values) 1) := by
    rw [PV_RunJoin_InterpolationCells73.complete values 0 (by decide),
      PV_RunJoin_InterpolationCells73.complete values 1 (by decide),hvalue 0,hvalue 1]
    exact sum
  obtain ⟨polynomial,interpolated,boundary⟩ := PV_RunJoin_NativeInterpolationBoundary73.running
    base heap box ops runtime world (PV_RunJoin_MergeArray35.array values) running hclaim sumCells
  have nativeWorker : host_work.map
      (host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnTupleUsizeResultQM31Error
        aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 oi)
      (Usize.wrapping_add 100#usize round) (count round)
      (oracle,point,round,assignments round)=ok evaluations := by
    rw [PV_RunJoin_RoundWorkerPlan69.native]
    exact worker
  have factored : host_sumcheck.prove_sumcheck_round
      aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 oi t output point running round oracle=
      PV_RunJoin_RoundAfterPolynomial72.run aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
        t output point running round (PV_RunJoin_MergeArray35.array polynomial) := by
    rw [PV_RunJoin_RoundWorkerReached69.reached]
    simp only [count,assignments,remaining] at nativeWorker
    simp only [PV_RunJoin_NativeQuarticTotal69.zero_source base heap box ops runtime world,nativeWorker,bind_tc_ok]
    exact PV_RunJoin_RoundAfterPolynomial72.reached _ t output point running round
      (assignments round) evaluations _ _ merged interpolated
  obtain ⟨challenge,claim,next,after,run,row,hash,len⟩ := PV_RunJoin_NativeRoundTail73.complete
    base heap box ops runtime world t output point round bound (PV_RunJoin_MergeArray35.array polynomial)
    running boundary order total outputSize
  exact ⟨Aeneas.Std.Array.set point round challenge,claim,next,after,by rw [factored];exact run,row,hash,len⟩

#print axioms complete
end R1Z.PV_RunJoin_NativeWorkerRound73
