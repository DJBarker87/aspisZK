import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee030
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2` (callee `prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop0`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (self : prover.Backend) (h1 : Slice aspis_core.field.QM31) (g : Array aspis_core.field.QM31 1024#usize) :
  ∃ next, prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2 (self := self) (h1 := h1) (g := g) =
    (prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2_loop0
      self h1 0#usize >>= next) := by
  unfold prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee030
