import PV_B3P_ScalarSemanticBinding13227
import PV_B3P_PartsBinding13227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std ProverRwFull PV_B3P_TopDown13227
set_option autoImplicit false
noncomputable section

def scalar_source_ports13 (base : ExternalTypes) (composition : CompositionFn13)
    (equality : Array SQ 10#usize → Array SQ 10#usize → Result SQ) : SourcePorts base :=
  ⟨PV_B3P_ScalarBinding13227.semantic_source13 base,source_selection13,parts_with13 composition equality⟩

section
variable (base : ExternalTypes)
local notation "terminal" => transported_reference base
/-- This composition consumes the newly extracted exact-span semantic body.
The native outer callback and changed-function links remain explicit. -/
theorem selected_scalar_callback13
    (ops : @ExternalFuns (PV_B3P_Install227.Types base))
    (composition : CompositionFn13)
    (equality : Array SQ 10#usize → Array SQ 10#usize → Result SQ)
    (wrapper : PV_B3P_Link_terminal_qm31 base ops (scalar_source_ports13 base composition equality))
    (hc : PV_B3P_Links13227.PV_B3P_Link_terminal_composition_parts composition)
    (he : PV_B3P_Links13227.PV_B3P_Link_terminal_equality_value equality)
    (self : @host_semantic.SemanticOracle (PV_B3P_Install227.Types base))
    (point : Array aspis_core.field.QM31 10#usize) :
    letI : ExternalTypes := PV_B3P_Install227.Types base
    ∀ claims,
      ops.op227 self.«public» claims point self.challenges =
        terminal self.«public» claims point self.challenges := by
  letI : ExternalTypes := PV_B3P_Install227.Types base
  exact PV_B3P_TopDown13227.selected_callback base ops (scalar_source_ports13 base composition equality)
    wrapper (PV_B3P_ScalarBinding13227.semantic_source_binding13 base) source_selection_binding13
    (parts_link13 composition equality hc he) self point
end

theorem scalar_links_satisfiable13 (base : ExternalTypes)
    (original : @ExternalFuns (PV_B3P_Install227.Types base)) :
    ∃ ops composition equality,
      PV_B3P_Link_terminal_qm31 base ops (scalar_source_ports13 base composition equality) ∧
      PV_B3P_Links13227.PV_B3P_Link_terminal_composition_parts composition ∧
      PV_B3P_Links13227.PV_B3P_Link_terminal_equality_value equality := by
  refine ⟨PV_B3P_Install227.actual base original,
    PV_B3P_227.reference_terminal.composition_parts,
    PV_B3P_227.reference_terminal.equality_value,?_,rfl,rfl⟩
  intro p claims point c
  exact Eq.trans (PV_B3P_Install227.actual_source base original p claims point c)
    (continuation_composes base
      (scalar_source_ports13 base PV_B3P_227.reference_terminal.composition_parts
        PV_B3P_227.reference_terminal.equality_value)
      (PV_B3P_ScalarBinding13227.semantic_source_binding13 base) source_selection_binding13
      (parts_link13 _ _ rfl rfl) p claims point c).symm
#print axioms selected_scalar_callback13
#print axioms scalar_links_satisfiable13
end
end PV_B3P_Binding13227
