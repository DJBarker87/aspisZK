import PV_B3P_SelectedValue226
import PV_B3P_NativePlan226
import PV_B3P_NativeIdentities226
import PV_B3P_ResultSpine226
import PV_B3P_Padding226
import PV_B3P_Nonvacuity226V3
namespace PV_B3P_Closure226
open Aeneas Aeneas.Std ProverRwFull
set_option autoImplicit false
noncomputable section

-- The native association is the separate, script-checked structural argument.
-- This theorem states the entire selected-reference Result without hypotheses.
theorem complete_result (base : ExternalTypes)
    (ops : @ExternalFuns (PV_B3P_Install226V3.Types base))
    (p : @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
      (PV_B3P_Install226V3.Types base)) :
    @ExternalFuns.op226 (PV_B3P_Install226V3.Types base)
      (PV_B3P_Install226V3.selected base ops) p =
      PV_B3P_Install226V3.transport (PV_B3P_EncodeLaw226.spec
        (PV_B3P_ProjectV3Law226.value (PV_B3P_PublicCarrier226V3.toSource base p))) := by
  rw [PV_B3P_Install226V3.source,PV_B3P_ProjectV3Law226.complete_source,
    PV_B3P_EncodeLaw226.complete_result]

theorem value (base : ExternalTypes)
    (ops : @ExternalFuns (PV_B3P_Install226V3.Types base))
    (p : @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
      (PV_B3P_Install226V3.Types base)) (out : alloc.vec.Vec U8)
    (h : @ExternalFuns.op226 (PV_B3P_Install226V3.Types base)
      (PV_B3P_Install226V3.selected base ops) p = .ok (.Ok out)) :
    out.val = PV_B3P_ByteLayout226V3.layout
      (PV_B3P_ProjectV3Law226.value (PV_B3P_PublicCarrier226V3.toSource base p)) :=
  PV_B3P_SelectedValue226.success_value base ops p out h

theorem nonvacuity (base : ExternalTypes)
    (ops : @ExternalFuns (PV_B3P_Install226V3.Types base)) (b : Bool) :
    ∃ p out, @ExternalFuns.op226 (PV_B3P_Install226V3.Types base)
      (PV_B3P_Install226V3.selected base ops) p = .ok (.Ok out) :=
  PV_B3P_Nonvacuity226V3.installed_success base ops b

#print axioms complete_result
#print axioms value
#print axioms nonvacuity
end
end PV_B3P_Closure226
