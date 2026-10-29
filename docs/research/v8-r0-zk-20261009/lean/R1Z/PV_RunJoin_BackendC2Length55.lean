import R1Z.PV_RunJoin_BackendC2HLength55
import R1Z.PV_RunJoin_BackendC2GLength55
import R1Z.PV_RunJoin_RecordAppend41
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BackendC2Length55
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
open prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments
variable [ExternalTypes] [ExternalFuns]

theorem complete (h1 : Slice aspis_core.field.QM31) (g : Array aspis_core.field.QM31 1024#usize) (self : prover.Backend) (hlen : self.messages.length=29) :
    Post (fun next => next.2.messages.length=29) (c2 self h1 g) := by
  unfold c2
  apply PV_RunJoin_RecordAppend41.bind_post (PV_RunJoin_BackendC2HLength55.complete h1 1024 0#usize self rfl hlen)
  intro self1 hlen1
  apply PV_RunJoin_RecordAppend41.bind_post (PV_RunJoin_BackendC2GLength55.complete g 1024 0#usize self1 rfl hlen1)
  intro self2 hlen2
  repeat first
  | exact hlen2
  | apply PV_RunJoin_ResultPost41.bind; intro value
  | split
#print axioms complete
end R1Z.PV_RunJoin_BackendC2Length55
