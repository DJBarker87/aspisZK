import R1Z.PV_RunJoin_NativeAssignment72
import R1Z.PV_RunJoin_NativeMerge72
import R1Z.PV_RunJoin_RoundWorkerPlan69
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeWorkerMerge72
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
open PV_RunJoin_SampleDomain34
abbrev Q := aspis_core.field.QM31

theorem complete {T H S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) (digest : aspis_core.digest.Digest32 H)
    (oi : host_sumcheck.Oracle T) (oracle : T) (point : Array Q 10#usize)
    (round : Usize) (bound : round.val<10)
    (evaluations : alloc.vec.Vec (core.result.Result Q r1_wire.Error))
    (worker : letI : ExternalTypes := types base
      letI : ExternalFuns := opsNative base heap box ops runtime world
      @host_work.map (types base) ops _ _
        (host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnTupleUsizeResultQM31Error digest oi)
        (Usize.wrapping_add 100#usize round) (count round)
        (oracle,point,round,assignments round)=ok evaluations)
    (size : evaluations.length=(count round).val)
    (agrees : ∀ i : Usize,i.val<evaluations.length →
      Slice.index_usize (alloc.vec.Vec.deref evaluations) i=
        @host_sumcheck.evaluate_assignment (types base) (opsNative base heap box ops runtime world)
          T oi oracle point round (assignments round) i)
    (evaluates : ∀ p,∃ q,oi.evaluate oracle p=ok (.Ok q)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops runtime world
    ∃ values,host_work.map
        (host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnTupleUsizeResultQM31Error digest oi)
        (Usize.wrapping_add 100#usize round) (count round)
        (oracle,point,round,assignments round)=ok evaluations ∧
      host_sumcheck.merge_evaluations (alloc.vec.Vec.deref evaluations) (assignments round)=ok (.Ok values) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  have positive := (assignments_bound round bound).1
  obtain ⟨values,hm⟩ := PV_RunJoin_NativeMerge72.complete base heap box ops runtime world round bound
    (alloc.vec.Vec.deref evaluations) size (fun i hi => by
      obtain ⟨out,ho⟩ := PV_RunJoin_NativeAssignment72.complete base heap box ops runtime world
        oi oracle point round (assignments round) i bound (Nat.ne_of_gt positive) evaluates
      exact ⟨out,(agrees i hi).trans ho⟩)
  refine ⟨values,?_,hm⟩
  rw [PV_RunJoin_RoundWorkerPlan69.native]
  exact worker

#print axioms complete
end R1Z.PV_RunJoin_NativeWorkerMerge72
