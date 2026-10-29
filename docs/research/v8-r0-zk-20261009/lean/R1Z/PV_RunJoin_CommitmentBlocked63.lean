import R1Z.PV_RunJoin_WorkerObstruction63
import R1Z.PV_RunJoin_PostBind63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CommitmentBlocked63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
variable [ExternalTypes] [ExternalFuns]

theorem build (denied : PV_RunJoin_WorkerObstruction63.Denied)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (domain : host_commitment.EncodingDomain) (time : host_commitment.CommitmentTime)
    (messages : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize))
    (variant : transport.Variant) (salts : Option host_commitment.PrivateSalts) :
    Post (fun status => match status with | .Err _ => True | .Ok _ => False)
      (host_commitment.Commitment.build hash domain time messages variant salts) := by
  unfold host_commitment.Commitment.build
  apply PV_RunJoin_ResultPost41.bind
  intro laneCount
  split
  · trivial
  · apply PV_RunJoin_ResultPost41.bind
    intro privateSalts
    apply PV_RunJoin_ResultPost41.bind
    intro invalid
    cases invalid with
    | true => trivial
    | false =>
      apply PV_RunJoin_ResultPost41.bind
      intro laneStatus
      cases laneStatus with
      | Err e => trivial
      | Ok lanes =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
        apply PV_RunJoin_PostBind63.guarded _ _ _ _
          (PV_RunJoin_WorkerObstruction63.encode denied domain messages variant (alloc.vec.Vec.deref lanes))
        intro encoded hencoded
        cases encoded with
        | Ok words => exact hencoded.elim
        | Err e => trivial

#print axioms build
end R1Z.PV_RunJoin_CommitmentBlocked63
