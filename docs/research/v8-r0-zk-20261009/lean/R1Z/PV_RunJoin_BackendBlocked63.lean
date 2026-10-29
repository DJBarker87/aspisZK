import R1Z.PV_RunJoin_CommitmentBlocked63
import R1Z.ProverRwOuterMapErr
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BackendBlocked63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
variable [ExternalTypes]

theorem c1 (ops : ExternalFuns)
    (mapErr : @ExternalFuns.op12 _ ops=@ProverRwOuterMapErr.map_err)
    (denied : @PV_RunJoin_WorkerObstruction63.Denied _ ops)
    (backend : prover.Backend)
    (columns : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize)
    (d : Array aspis_core.field.QM31 1024#usize) :
    letI : ExternalFuns := ops
    Post (fun pair => match pair.1 with | .Err _ => True | .Ok _ => False)
      (prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1 backend columns d) := by
  letI : ExternalFuns := ops
  unfold prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1
  apply PV_RunJoin_ResultPost41.bind
  intro first
  apply PV_RunJoin_ResultPost41.bind
  intro second
  apply PV_RunJoin_ResultPost41.bind
  intro privateSalts
  cases privateSalts with
  | Err e => trivial
  | Ok salts =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
      host_commitment.Commitment.new_salted]
    apply PV_RunJoin_PostBind63.guarded _ _ _ _
      (PV_RunJoin_CommitmentBlocked63.build denied second.hash second.domain .C1
        (alloc.vec.Vec.deref second.messages) second.variant (some salts))
    intro status hstatus
    cases status with
    | Ok commitment => exact hstatus.elim
    | Err e =>
      simp only [core.result.Result.map_err,mapErr,ProverRwOuterMapErr.map_err,
        prover.CommitmentsBackend.c1.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError,
        prover.CommitmentsBackend.c1.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
        bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
      trivial

#print axioms c1
end R1Z.PV_RunJoin_BackendBlocked63
