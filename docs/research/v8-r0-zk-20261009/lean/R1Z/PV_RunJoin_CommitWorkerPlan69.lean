import R1Z.PV_RunJoin_CommitWorkerReached69
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CommitWorkerPlan69
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63 PV_RunJoin_Sequential64

/-- Actual commitment prefix reified as reserve THEN worker. The worker
continuation executes at this reservation's exact post-world. A subsequent
source reservation still needs fixed-world/threaded-world compatibility. -/
theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (domain : host_commitment.EncodingDomain)
    (messages : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize))
    (variant : transport.Variant) (lanes : Slice Usize)
    (reserve : (PV_RunJoin_AllocatorWorld63.execute runtime world
      (alloc.vec.Vec.new host_commitment.Word) (Slice.len lanes)).returned=.ok ())
    (valid : @host_commitment.validate_commitment_lanes (types base)
      (opsNative base heap box ops runtime world) messages lanes=ok (.Ok ())) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops runtime world
    execute runtime (.reserve (alloc.vec.Vec.new host_commitment.Word) (Slice.len lanes)
      (fun _ words => .worker
        host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnTupleUsizeResultWordError
        200#usize (Slice.len lanes) (domain,messages,variant,lanes)
        (fun encoded => .step (PV_RunJoin_CommitWorkerReached69.tail words encoded) Plan.done))) world=
      (do let value ← host_commitment.encode_commitment_words domain messages variant lanes
          ok (value,(PV_RunJoin_AllocatorWorld63.execute runtime world
            (alloc.vec.Vec.new host_commitment.Word) (Slice.len lanes)).world)) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  rw [PV_RunJoin_CommitWorkerReached69.reached base heap box ops runtime world domain messages variant lanes reserve valid]
  simp only [execute,bind_assoc_eq]

#print axioms complete
end R1Z.PV_RunJoin_CommitWorkerPlan69
