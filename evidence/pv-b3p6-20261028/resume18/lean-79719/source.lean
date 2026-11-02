import PV_B3P_LocalClosure557227
import PV_B3P_DependencyClosure557227
import PV_B3P_GroupCallback13227
namespace PV_B3P_Closure557227
open Aeneas Aeneas.Std ProverRwFull PV_B3P_TopDown13227 PV_B3P_Binding13227
set_option autoImplicit false
noncomputable section
/-- The exact remaining source-wrapper obligation at a supplied dictionary.
It exposes selection, public conversion, terminal parts and both Result layers;
it is not discharged by the partial catalogue or by choosing an installation. -/
def DeployedWrapper557 (base : ExternalTypes)
    (ops : @ExternalFuns (PV_B3P_Install227.Types base)) : Prop :=
  PV_B3P_Link_terminal_qm31 base ops
    (source_ports13 base local_bodies557.body6 local_bodies557.body7)

section
variable (base : ExternalTypes)
local notation "terminal" => transported_reference base
/-- Conditional residual reduction, NOT the requested unconditional deployed
bridge. Its sole residual argument is visibly retained in the type. All local
changed-body links are fixed and proved, rather than additional hypotheses. -/
theorem selected_callback_residual557
    (ops : @ExternalFuns (PV_B3P_Install227.Types base))
    (wrapper : DeployedWrapper557 base ops)
    (self : @host_semantic.SemanticOracle (PV_B3P_Install227.Types base))
    (point : Array aspis_core.field.QM31 10#usize) :
    letI : ExternalTypes := PV_B3P_Install227.Types base
    ∀ claims,
      ops.op227 self.«public» claims point self.challenges =
        terminal self.«public» claims point self.challenges := by
  letI : ExternalTypes := PV_B3P_Install227.Types base
  exact selected_callback13 base ops local_bodies557.body6 local_bodies557.body7 wrapper
    local_links557.link6 local_links557.link7 self point
end

/-- A witness for the FIXED interpretations' joint local links; no dictionary
is constructed and no native wrapper witness is asserted. -/
theorem joint_local_closure557 (α : Type) :
    PV_B3P_Correct14227.CorrectedLinks14 local_bodies557
      PV_B3P_Correct14227.frozen_calls14 PV_B3P_Correct14227.constructor14 57#usize ∧
    PV_B3P_Groups14227.PV_B3P_Link_std_dependency_closure14
      (Signature557 α) (source557 α) (model557 α) :=
  ⟨local_links557,partial_closure557 α⟩

#print axioms selected_callback_residual557
#print axioms joint_local_closure557
end
end PV_B3P_Closure557227
