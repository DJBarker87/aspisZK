import R1Z.PV_RunJoin_RoundWorkerReached69
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundWorkerPlan69
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_Sequential64 PV_RunJoin_NativeResidual63
abbrev Q := aspis_core.field.QM31
variable [ExternalTypes] [ExternalFuns]

theorem complete {S E H F : Type} (runtime : PV_RunJoin_AllocatorWorld63.Runtime S E)
    (world : PV_FXM_ReserveWorld.World S E)
    (digest : aspis_core.digest.Digest32 H) (oracleInst : host_sumcheck.Oracle F)
    (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec U8)
    (point : Array Q 10#usize) (running : Q) (round : Usize) (oracle : F) :
    (let assignments := Usize.wrapping_shl 1#usize (UScalar.cast .U32 (Usize.wrapping_sub 9#usize round))
     execute runtime (.step aspis_core.field.QM31.ZERO (fun _ => .worker
       (host_sumcheck.prove_sumcheck_round.closure.Insts.CoreOpsFunctionFnTupleUsizeResultQM31Error digest oracleInst)
       (Usize.wrapping_add 100#usize round) (Usize.wrapping_mul 28#usize assignments)
       (oracle,point,round,assignments)
       (fun evaluations => .step (PV_RunJoin_RoundWorkerReached69.tail digest transcript output point
         running round assignments evaluations) Plan.done))) world)=
      (do let value ← host_sumcheck.prove_sumcheck_round digest oracleInst transcript output point running round oracle
          ok (value,world)) := by
  rw [PV_RunJoin_RoundWorkerReached69.reached]
  simp only [execute,bind_assoc_eq]

end R1Z.PV_RunJoin_RoundWorkerPlan69
namespace R1Z.PV_RunJoin_RoundWorkerPlan69
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
/-- The actual immutable native dictionary preserves the returned vector
itself, hence all source length checks; this is not mere existential success. -/
theorem native {T G S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (inst : core.ops.function.Fn G Usize T) (cost count : Usize) (closure : G) :
    @host_work.map (types base) (opsNative base heap box ops runtime world) T G inst cost count closure=
      @host_work.map (types base) ops T G inst cost count closure := by
  change @ExternalFuns.op257 (types base) (opsNative base heap box ops runtime world) T G inst cost count closure=
    @ExternalFuns.op257 (types base) ops T G inst cost count closure
  rw [PV_RunJoin_NativeFrames63.op257]

#print axioms complete
#print axioms native
end R1Z.PV_RunJoin_RoundWorkerPlan69
