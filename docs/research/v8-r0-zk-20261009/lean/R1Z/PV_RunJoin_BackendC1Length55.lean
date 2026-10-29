import R1Z.PV_RunJoin_BackendC1ColumnsLength55
import R1Z.PV_RunJoin_BackendC1DLength55
import R1Z.PV_RunJoin_RecordAppend41
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BackendC1Length55
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
open prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments
variable [ExternalTypes] [ExternalFuns]

theorem complete (columns : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize)
    (d : Array aspis_core.field.QM31 1024#usize) (self : prover.Backend) (hlen : self.messages.length=29) :
    Post (fun next => next.2.messages.length=29) (c1 self columns d) := by
  unfold c1
  apply PV_RunJoin_RecordAppend41.bind_post (PV_RunJoin_BackendC1ColumnsLength55.complete columns 26 0#usize self rfl hlen)
  intro self1 hlen1
  apply PV_RunJoin_RecordAppend41.bind_post (PV_RunJoin_BackendC1DLength55.complete d 1024 0#usize self1 rfl hlen1)
  intro self2 hlen2
  repeat first
  | exact hlen2
  | apply PV_RunJoin_ResultPost41.bind; intro value
  | split
#print axioms complete
end R1Z.PV_RunJoin_BackendC1Length55
