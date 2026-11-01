import R1Z.PV_RunJoin_BackendC2HFrame66
import R1Z.PV_RunJoin_BackendC2GFrame66
import R1Z.PV_RunJoin_RecordAppend41
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BackendC2Frame66
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
open prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments
variable [ExternalTypes] [ExternalFuns]

theorem complete (self : prover.Backend) (h1 : Slice aspis_core.field.QM31)
    (g : Array aspis_core.field.QM31 1024#usize) :
    Post (fun pair => pair.2.c1=self.c1) (c2 self h1 g) := by
  unfold c2
  apply PV_RunJoin_RecordAppend41.bind_post
    (PV_RunJoin_BackendC2HFrame66.complete h1 1024 0#usize self rfl)
  intro self1 hfirst
  apply PV_RunJoin_RecordAppend41.bind_post
    (PV_RunJoin_BackendC2GFrame66.complete g 1024 0#usize self1 rfl)
  intro self2 hsecond
  have same : self2.c1=self.c1 := hsecond.trans hfirst
  repeat first
  | exact same
  | apply PV_RunJoin_ResultPost41.bind; intro value
  | split

#print axioms complete
end R1Z.PV_RunJoin_BackendC2Frame66
