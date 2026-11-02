import R1Z.PV_RunJoin_NativeQuarticEq72
import R1Z.PV_RunJoin_RoundThread38
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SumcheckFinish72
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
abbrev Q := aspis_core.field.QM31

theorem complete {H T S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) (oi : host_sumcheck.Oracle T)
    (oracle : T) (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec U8)
    (point : Array Q 10#usize) (running : Q)
    (evaluates : oi.evaluate oracle point=ok (.Ok running)) :
    @PV_RunJoin_RoundThread38.finish (types base) (opsNative base heap box ops runtime world)
      H T oi transcript output point running oracle=ok (.Ok (point,running),transcript,output) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  simp only [PV_RunJoin_RoundThread38.finish,evaluates,
    core.result.Result.Insts.CoreOpsTry.branch,
    PV_RunJoin_NativeQuarticEq72.ne_self base heap box ops runtime world,
    bind_tc_ok,Bool.false_eq_true,if_false]

#print axioms complete
end R1Z.PV_RunJoin_SumcheckFinish72
