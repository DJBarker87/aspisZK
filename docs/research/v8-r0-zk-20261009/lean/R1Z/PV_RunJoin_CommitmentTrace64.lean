import R1Z.PV_RunJoin_PostEquation60
import R1Z.ProverRwFullFuns
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CommitmentTrace64
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
variable [ExternalTypes] [ExternalFuns]

def Trace (hash : aspis_core.digest.LegacyHashFn) (time : host_commitment.CommitmentTime)
    (salts : Option host_commitment.PrivateSalts) (c : host_commitment.Commitment) : Prop :=
  c.time=time ∧ c.private_salts=salts ∧
  host_commitment.commitment_lanes time=ok (.Ok c.lanes) ∧
  ∃ leaves, host_commitment.commitment_leaves hash time (alloc.vec.Vec.deref c.lanes)
    (alloc.vec.Vec.deref c.words) salts=ok (.Ok leaves)

theorem source (hash : aspis_core.digest.LegacyHashFn) (domain : host_commitment.EncodingDomain)
    (time : host_commitment.CommitmentTime)
    (messages : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize))
    (variant : transport.Variant) (salts : Option host_commitment.PrivateSalts) :
    Post (fun status => match status with | .Err _ => True | .Ok c => Trace hash time salts c)
      (host_commitment.Commitment.build hash domain time messages variant salts) := by
  unfold host_commitment.Commitment.build
  apply PV_RunJoin_ResultPost41.bind
  intro laneCount
  split
  · trivial
  · apply PV_RunJoin_ResultPost41.bind
    intro saltRef
    apply PV_RunJoin_ResultPost41.bind
    intro denied
    cases denied with
    | true => trivial
    | false =>
      simp only [Bool.false_eq_true,if_false]
      apply PV_RunJoin_PostEquation60.bind
      intro laneStatus hlane
      cases laneStatus with
      | Err e => trivial
      | Ok lanes =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
        apply PV_RunJoin_ResultPost41.bind
        intro wordStatus
        cases wordStatus with
        | Err e => trivial
        | Ok words =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
          apply PV_RunJoin_PostEquation60.bind
          intro leafStatus hleaf
          cases leafStatus with
          | Err e => trivial
          | Ok leaves =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
            apply PV_RunJoin_ResultPost41.bind
            intro treeOption
            cases treeOption with
            | none => trivial
            | some tree =>
              exact ⟨rfl,rfl,hlane,leaves,hleaf⟩

theorem complete (hash : aspis_core.digest.LegacyHashFn) (domain : host_commitment.EncodingDomain)
    (time : host_commitment.CommitmentTime)
    (messages : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize))
    (variant : transport.Variant) (salts : Option host_commitment.PrivateSalts)
    (c : host_commitment.Commitment)
    (success : host_commitment.Commitment.build hash domain time messages variant salts=ok (.Ok c)) :
    Trace hash time salts c :=
  PV_RunJoin_ResultPost41.success _ _ (.Ok c) (source hash domain time messages variant salts) success

#print axioms source
#print axioms complete
end R1Z.PV_RunJoin_CommitmentTrace64
