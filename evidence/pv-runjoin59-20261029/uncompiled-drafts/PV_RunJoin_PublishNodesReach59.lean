import R1Z.PV_RunJoin_PublishReach54
import R1Z.PV_RunJoin_ResultCapture59
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PublishNodesReach59
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_ResultPost
variable [ExternalTypes] [ExternalFuns]

def Reached (p : prover.Publication) (proof : alloc.vec.Vec U8) (offset : Usize) : Prop :=
  ∃ (out : alloc.vec.Vec U8) (cc1 cc2 : host_commitment.Commitment),
    out.length=offset.val ∧
    prover.append_node_slots out cc1 cc2 p.tree p.queries=ok (.Ok proof)

def Good (p : prover.Publication) (offset : Usize) :
    core.result.Result (alloc.vec.Vec U8) verifier.Error → Prop
  | .Ok proof => Reached p proof offset
  | .Err _ => True

theorem residual (p : prover.Publication) (offset : Usize)
    (r : core.result.Result core.convert.Infallible verifier.Error) :
    Post (Good p offset)
      (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (alloc.vec.Vec U8) (core.convert.FromSame verifier.Error) r) := by
  cases r with
  | Ok impossible => cases impossible
  | Err e => intro x h; cases h; trivial

theorem post (variant : transport.Variant) (p : prover.Publication) (offset : Usize)
    (hoffset : compact.OFF_NODES=ok offset) :
    Post (Good p offset) (prover.publish_compact variant p) := by
  unfold prover.publish_compact
  rw [hoffset]
  simp only [bind_tc_ok]
  repeat' first
    | exact residual p offset _
    | apply PV_RunJoin_ResultCapture59.guard; intro hguard
    | progress simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    | apply PV_RunJoin_ResultCapture59.bind; intro x hx
    | dsimp only [Aeneas.Std.uncurry]
    | split
  all_goals trace_state

theorem complete (variant : transport.Variant) (p : prover.Publication)
    (proof : alloc.vec.Vec U8) (offset : Usize)
    (hoffset : compact.OFF_NODES=ok offset)
    (success : prover.publish_compact variant p=ok (.Ok proof)) : Reached p proof offset :=
  post variant p offset hoffset (.Ok proof) success

#print axioms Reached
#print axioms Good
#print axioms residual
#print axioms post
#print axioms complete
end R1Z.PV_RunJoin_PublishNodesReach59
