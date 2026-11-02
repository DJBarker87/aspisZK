import R1Z.PV_RunJoin_NativeAllocator69
import R1Z.PV_RunJoin_PreparedMapErr48
import R1Z.PV_RunJoin_Sequential64
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CommitWorkerReached69
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
variable [ExternalTypes] [ExternalFuns]
/-- Preserve both processing loops, the complete returned vector and every
inner error. No length or value of the worker result is substituted. -/
def tail (words : alloc.vec.Vec host_commitment.Word)
    (encoded : alloc.vec.Vec (core.result.Result host_commitment.Word aspis_core.r0.Error)) :
    Result (core.result.Result (alloc.vec.Vec host_commitment.Word) aspis_core.r0.Error) := do
  let encoded1 ← host_commitment.encode_commitment_words_loop0 encoded 0#usize
  let (words1,pending) ← host_commitment.encode_commitment_words_loop1 words encoded1
  match pending with
  | none => ok (.Ok words1)
  | some status => ok status

end R1Z.PV_RunJoin_CommitWorkerReached69
namespace R1Z.PV_RunJoin_CommitWorkerReached69
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63

theorem reached {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (domain : host_commitment.EncodingDomain)
    (messages : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize))
    (variant : transport.Variant) (lanes : Slice Usize)
    (reserve : letI : ExternalTypes := types base
      (PV_RunJoin_AllocatorWorld63.execute runtime world
      (alloc.vec.Vec.new host_commitment.Word) (Slice.len lanes)).returned=.ok ())
    (valid : @host_commitment.validate_commitment_lanes (types base)
      (opsNative base heap box ops runtime world) messages lanes=ok (.Ok ())) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops runtime world
    @host_commitment.encode_commitment_words (types base) (opsNative base heap box ops runtime world)
      domain messages variant lanes=
      (do let encoded ← @host_work.map (types base) (opsNative base heap box ops runtime world) _ _
            host_commitment.encode_commitment_words.closure_1.Insts.CoreOpsFunctionFnTupleUsizeResultWordError
            200#usize (Slice.len lanes) (domain,messages,variant,lanes)
          @tail (types base) (opsNative base heap box ops runtime world)
            (alloc.vec.Vec.new host_commitment.Word) encoded) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  have hr := (PV_RunJoin_NativeAllocator69.success_iff base heap box ops runtime world Global
    (alloc.vec.Vec.new host_commitment.Word) (Slice.len lanes)).mpr reserve
  have hm : core.result.Result.map_err
      host_commitment.encode_commitment_words.closure.Insts.CoreOpsFunctionFnOnceTupleTryReserveErrorError
      (.Ok ()) ()=ok (.Ok ()) := by
    change @ExternalFuns.op12 (types base)
      (PV_RunJoin_WeightInstalled46.selected (PV_RunJoin_NativeResidual62.baseTypes base) heap box
        (residual base ops runtime world)) _ _ _ _ _ _ _=_
    rw [PV_RunJoin_PreparedMapErr48.field (PV_RunJoin_NativeResidual62.baseTypes base) heap box
      (residual base ops runtime world)]
    rfl
  simp only [host_commitment.encode_commitment_words,hr,hm,valid,
    core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry]
  rfl

#print axioms tail
#print axioms reached
end R1Z.PV_RunJoin_CommitWorkerReached69
