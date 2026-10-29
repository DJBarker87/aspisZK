import PV_B3P_PartsBinding13227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std ProverRwFull PV_B3P_TopDown13227
set_option autoImplicit false
noncomputable section
/-- Joint satisfiability of the three core links. This is an explicit model
instance, not an assertion that the deployed callback is the installed one. -/
theorem core_links_satisfiable13 (base : ExternalTypes)
    (original : @ExternalFuns (PV_B3P_Install227.Types base)) :
    ∃ ops composition equality,
      PV_B3P_Link_terminal_qm31 base ops (source_ports13 base composition equality) ∧
      PV_B3P_Links13227.PV_B3P_Link_terminal_composition_parts composition ∧
      PV_B3P_Links13227.PV_B3P_Link_terminal_equality_value equality := by
  refine ⟨PV_B3P_Install227.actual base original,
    PV_B3P_227.reference_terminal.composition_parts,
    PV_B3P_227.reference_terminal.equality_value, ?_, rfl, rfl⟩
  intro p claims point c
  exact Eq.trans (PV_B3P_Install227.actual_source base original p claims point c)
    (continuation_composes base
      (source_ports13 base PV_B3P_227.reference_terminal.composition_parts
        PV_B3P_227.reference_terminal.equality_value)
      (semantic_source_binding13 base) source_selection_binding13
      (parts_link13 _ _ rfl rfl) p claims point c).symm
#print axioms core_links_satisfiable13
end
end PV_B3P_Binding13227
