import PV_B3P_LinkGroup13227
import PV_B3P_SkeletonWitness13227
namespace PV_B3P_Groups13227
open Aeneas Aeneas.Std ProverRwFull PV_B3P_Binding13227 PV_B3P_TopDown13227
set_option autoImplicit false
noncomputable section
section
variable (base : ExternalTypes)
local notation "terminal" => transported_reference base
/-- Function-group composition. Native instantiation, missing wrappers, D188,
and the complete dependency/source coverage remain independent obligations. -/
theorem selected_from_function_links13
    (ops : @ExternalFuns (PV_B3P_Install227.Types base))
    (bodies : ChangedBodies13)
    (wrapper : PV_B3P_Link_terminal_qm31 base ops
      (source_ports13 base bodies.body6 bodies.body7))
    (changed : PV_B3P_Link_changed_bodies bodies)
    (self : @host_semantic.SemanticOracle (PV_B3P_Install227.Types base))
    (point : Array aspis_core.field.QM31 10#usize) :
    letI : ExternalTypes := PV_B3P_Install227.Types base
    ∀ claims,
      ops.op227 self.«public» claims point self.challenges =
        terminal self.«public» claims point self.challenges := by
  letI : ExternalTypes := PV_B3P_Install227.Types base
  exact selected_callback13 base ops bodies.body6 bodies.body7 wrapper (changed.2.2.2.2.2.2.1) (changed.2.2.2.2.2.2.2.1) self point
end

theorem function_group_joint_witness13 (base : ExternalTypes)
    (original : @ExternalFuns (PV_B3P_Install227.Types base)) :
    ∃ ops bodies,
      PV_B3P_Link_terminal_qm31 base ops
        (source_ports13 base bodies.body6 bodies.body7) ∧
      PV_B3P_Link_changed_bodies bodies := by
  refine ⟨PV_B3P_Install227.actual base original,explicit_model_bodies13,?_,changed_bodies_satisfiable13⟩
  intro p claims point c
  exact Eq.trans (PV_B3P_Install227.actual_source base original p claims point c)
    (continuation_composes base
      (source_ports13 base PV_B3P_227.reference_terminal.composition_parts
        PV_B3P_227.reference_terminal.equality_value)
      (semantic_source_binding13 base) source_selection_binding13
      (parts_link13 _ _ rfl rfl) p claims point c).symm
#print axioms selected_from_function_links13
#print axioms function_group_joint_witness13
end
end PV_B3P_Groups13227
