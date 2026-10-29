import PV_B3P_TerminalSource15227
import PV_B3P_SelectedCorrected14227
namespace PV_B3P_Terminal15227
open Aeneas Aeneas.Std ProverRwFull PV_B3P_TopDown13227 PV_B3P_Binding13227
set_option autoImplicit false
noncomputable section

def terminal_native15 (base : ExternalTypes) (native : SourcePorts base)
    (p : Public base) (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
    (point : Array aspis_core.field.QM31 10#usize) (c : aspis_core.state_only_prefix.r0.Challenges) :=
  PV_B3P_Install227.transport (terminal_source15 base native p claims point c)

def source_install15 (base : ExternalTypes)
    (original : @ExternalFuns (PV_B3P_Install227.Types base)) (native : SourcePorts base) :
    @ExternalFuns (PV_B3P_Install227.Types base) :=
  { original with op227 := terminal_native15 base native }

theorem source_install_wrapper15 (base : ExternalTypes)
    (original : @ExternalFuns (PV_B3P_Install227.Types base)) (native : SourcePorts base) :
    PV_B3P_Link_terminal_qm31 base (source_install15 base original native) native := by
  intro p claims point c
  exact congrArg PV_B3P_Install227.transport (terminal_source_binding15 base native p claims point c)

/-- One concrete model instance jointly satisfies the wrapper and all corrected
function links. This witness is never labelled deployed native closure. -/
theorem native_model_joint_witness15 (base : ExternalTypes)
    (original : @ExternalFuns (PV_B3P_Install227.Types base)) :
    let native := source_ports13 base PV_B3P_227.reference_terminal.composition_parts
      PV_B3P_227.reference_terminal.equality_value
    PV_B3P_Link_terminal_qm31 base (source_install15 base original native) native ∧
      PV_B3P_Correct14227.CorrectedLinks14 PV_B3P_Correct14227.corrected_model_bodies14
        PV_B3P_Correct14227.frozen_calls14 PV_B3P_Correct14227.constructor14 57#usize := by
  exact ⟨source_install_wrapper15 base original _,PV_B3P_Correct14227.corrected_links_witness14⟩
#print axioms source_install_wrapper15
#print axioms native_model_joint_witness15
end
end PV_B3P_Terminal15227
