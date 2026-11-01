import R1Z.PV_RunJoin_PostEquation60
import R1Z.ProverRwOuterMapErr
import R1Z.ProverRwFullFuns
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BackendConstructor66
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
variable [ExternalTypes] [ext : ExternalFuns]

def Built (c : host_commitment.Commitment) : Prop :=
  ∃ (hash : aspis_core.digest.LegacyHashFn) (domain : host_commitment.EncodingDomain)
    (time : host_commitment.CommitmentTime)
    (messages : Slice (Array aspis_core.field.wide_exact.WideExact 1024#usize))
    (variant : transport.Variant) (salts : host_commitment.PrivateSalts),
    host_commitment.Commitment.build hash domain time messages variant (some salts)=ok (.Ok c)

theorem c1 (mapErr : @ExternalFuns.op12 _ ext = @ProverRwOuterMapErr.map_err)
    (self : prover.Backend)
    (columns : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize)
    (d : Array aspis_core.field.QM31 1024#usize) :
    Post (fun pair => match pair.1 with
      | .Err _ => True
      | .Ok _ => ∃ c, pair.2.c1=some c ∧ Built c)
      (prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1 self columns d) := by
  unfold prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1
  apply PV_RunJoin_ResultPost41.bind
  intro self1
  apply PV_RunJoin_ResultPost41.bind
  intro self2
  apply PV_RunJoin_ResultPost41.bind
  intro status
  cases status with
  | Err e => trivial
  | Ok salts =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    apply PV_RunJoin_PostEquation60.bind
    intro status hbuild
    change Post _ ((ext.op12 _ status ()) >>= _)
    rw [mapErr]
    cases status with
    | Err e =>
      simp only [ProverRwOuterMapErr.map_err,
        prover.CommitmentsBackend.c1.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError,
        prover.CommitmentsBackend.c1.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,bind_tc_ok]
      trivial
    | Ok c =>
      simp only [ProverRwOuterMapErr.map_err,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
      apply PV_RunJoin_ResultPost41.bind
      intro root
      exact ⟨c,rfl,self2.hash,self2.domain,host_commitment.CommitmentTime.C1,
        alloc.vec.Vec.deref self2.messages,self2.variant,salts,hbuild⟩

theorem c2 (mapErr : @ExternalFuns.op12 _ ext = @ProverRwOuterMapErr.map_err)
    (self : prover.Backend)
    (h1 : Slice aspis_core.field.QM31)
    (g : Array aspis_core.field.QM31 1024#usize) :
    Post (fun pair => match pair.1 with
      | .Err _ => True
      | .Ok _ => ∃ c, pair.2.c2=some c ∧ Built c)
      (prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2 self h1 g) := by
  unfold prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2
  apply PV_RunJoin_ResultPost41.bind
  intro self1
  apply PV_RunJoin_ResultPost41.bind
  intro self2
  apply PV_RunJoin_ResultPost41.bind
  intro status
  cases status with
  | Err e => trivial
  | Ok salts =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    apply PV_RunJoin_PostEquation60.bind
    intro status hbuild
    change Post _ ((ext.op12 _ status ()) >>= _)
    rw [mapErr]
    cases status with
    | Err e =>
      simp only [ProverRwOuterMapErr.map_err,
        prover.CommitmentsBackend.c2.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError,
        prover.CommitmentsBackend.c2.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,bind_tc_ok]
      trivial
    | Ok c =>
      simp only [ProverRwOuterMapErr.map_err,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
      apply PV_RunJoin_ResultPost41.bind
      intro root
      exact ⟨c,rfl,self2.hash,self2.domain,host_commitment.CommitmentTime.C2,
        alloc.vec.Vec.deref self2.messages,self2.variant,salts,hbuild⟩

#print axioms c2
#print axioms Built
#print axioms c1
end R1Z.PV_RunJoin_BackendConstructor66
