import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee015
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle.evaluate` (callee `host_semantic.point_claims`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (self : host_semantic.SemanticOracle) (point : Array aspis_core.field.QM31 10#usize) :
  ∃ next, host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle.evaluate (self := self) (point := point) =
    (host_semantic.point_claims self.columns point >>= next) := by
  unfold host_semantic.SemanticOracle.Insts.Aspis_r1_cost_probeHost_sumcheckOracle.evaluate
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee015
