import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee029
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1` (callee `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (self : prover.Backend) (columns : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize) (d : Array aspis_core.field.QM31 1024#usize) :
  ∃ next, prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1 (self := self) (columns := columns) (d := d) =
    (prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1_loop0
      self columns 0#usize >>= next) := by
  unfold prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee029
