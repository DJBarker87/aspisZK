from pathlib import Path
L=Path('evidence/pv-b3p6-20261028/lean')
s='''import PV_B3P_JointSourceModels15227
import PV_B3P_TerminalInstall15227
namespace PV_B3P_Bridge15227
open Aeneas Aeneas.Std ProverRwFull PV_B3P_TopDown13227 PV_B3P_Binding13227
open PV_B3P_Correct14227 PV_B3P_Native15227
set_option autoImplicit false
noncomputable section
section
variable (base : ExternalTypes)
local notation "terminal" => transported_reference base
/-- Model composition has the unchanged runjoin conclusion. The deployed
source wrapper and every outstanding native dependency are still obligations. -/
theorem selected_callback15 (ops : @ExternalFuns (PV_B3P_Install227.Types base))
    (wrapper : PV_B3P_Link_terminal_qm31 base ops
      (source_ports13 base joint_source_models15.body6 joint_source_models15.body7))
    (self : @host_semantic.SemanticOracle (PV_B3P_Install227.Types base))
    (point : Array aspis_core.field.QM31 10#usize) :
    letI : ExternalTypes := PV_B3P_Install227.Types base
    ∀ claims,
      ops.op227 self.«public» claims point self.challenges =
        terminal self.«public» claims point self.challenges := by
  letI : ExternalTypes := PV_B3P_Install227.Types base
  exact selected_callback14 base ops joint_source_models15 frozen_calls14 constructor14
    57#usize wrapper joint_source_links15 self point
end

theorem bridge_joint_witness15 (base : ExternalTypes)
    (original : @ExternalFuns (PV_B3P_Install227.Types base)) :
    ∃ ops,
      PV_B3P_Link_terminal_qm31 base ops
        (source_ports13 base joint_source_models15.body6 joint_source_models15.body7) ∧
      CorrectedLinks14 joint_source_models15 frozen_calls14 constructor14 57#usize := by
  exact ⟨PV_B3P_Terminal15227.source_install15 base original _,
    PV_B3P_Terminal15227.source_install_wrapper15 base original _,joint_source_links15⟩
#print axioms selected_callback15
#print axioms bridge_joint_witness15
end
end PV_B3P_Bridge15227
''';(L/'PV_B3P_JointBridge15227.lean').write_text(s)
