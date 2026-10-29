import PV_B3P_CorrectedGroup14227
import PV_B3P_GroupCallback13227
namespace PV_B3P_Correct14227
open Aeneas Aeneas.Std ProverRwFull PV_B3P_TopDown13227 PV_B3P_Binding13227 PV_B3P_Groups13227
set_option autoImplicit false
noncomputable section
section
variable (base : ExternalTypes)
local notation "terminal" => transported_reference base
/-- The corrected group still proves exactly the bridge hypothesis. The native
wrapper and all other function links remain explicit hypotheses. -/
theorem selected_callback14 (ops : @ExternalFuns (PV_B3P_Install227.Types base))
    (bodies : ChangedBodies13) (called : U16 → Prop)
    (constructor : Usize → SelectorFn) (blocks : Usize)
    (wrapper : PV_B3P_Link_terminal_qm31 base ops (source_ports13 base bodies.body6 bodies.body7))
    (links : CorrectedLinks14 bodies called constructor blocks)
    (self : @host_semantic.SemanticOracle (PV_B3P_Install227.Types base))
    (point : Array aspis_core.field.QM31 10#usize) :
    letI : ExternalTypes := PV_B3P_Install227.Types base
    ∀ claims,
      ops.op227 self.«public» claims point self.challenges =
        terminal self.«public» claims point self.challenges := by
  letI : ExternalTypes := PV_B3P_Install227.Types base
  exact selected_callback13 base ops bodies.body6 bodies.body7 wrapper links.link6 links.link7 self point
end

theorem corrected_callback_joint_witness14 (base : ExternalTypes)
    (original : @ExternalFuns (PV_B3P_Install227.Types base)) :
    ∃ ops bodies called constructor blocks,
      PV_B3P_Link_terminal_qm31 base ops (source_ports13 base bodies.body6 bodies.body7) ∧
      CorrectedLinks14 bodies called constructor blocks := by
  obtain ⟨ops,composition,equality,wrapper,hc,he⟩ := core_links_satisfiable13 base original
  -- Choose one explicit instance for every body and for the same wrapper.
  refine ⟨PV_B3P_Install227.actual base original,corrected_model_bodies14,
    frozen_calls14,constructor14,57#usize,?_,corrected_links_witness14⟩
  intro p claims point c
  exact Eq.trans (PV_B3P_Install227.actual_source base original p claims point c)
    (continuation_composes base
      (source_ports13 base PV_B3P_227.reference_terminal.composition_parts
        PV_B3P_227.reference_terminal.equality_value)
      (semantic_source_binding13 base) source_selection_binding13
      (parts_link13 _ _ rfl rfl) p claims point c).symm
#print axioms selected_callback14
#print axioms corrected_callback_joint_witness14
end
end PV_B3P_Correct14227
