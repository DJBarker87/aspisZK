import PV_B3P_CompositionCallees557227
import PV_B3P_BridgeResidual557227
namespace PV_B3P_Closure557227
open Aeneas Aeneas.Std ProverRwFull PV_B3P_TopDown13227 PV_B3P_Binding13227
set_option autoImplicit false
noncomputable section
/-- Whole terminal continuation with the composed source callers. This is an
interpreter, not a replacement or an installation of the deployed dictionary. -/
def composed_ports557 (base : ExternalTypes) : SourcePorts base :=
  ⟨semantic_source13 base,source_selection13,
    parts_with13 composition_callees557 local_bodies557.body7⟩

theorem composed_ports_eq557 (base : ExternalTypes) :
    composed_ports557 base =
      source_ports13 base local_bodies557.body6 local_bodies557.body7 := by
  have composition : composition_callees557 = local_bodies557.body6 :=
    Eq.trans composition_callees_reference557 local_links557.link6.symm
  unfold composed_ports557
  rw [composition]
  rfl

/-- Complete Result equality for arbitrary claims, public, point and challenges
on the declared carrier. No successful-result or canonicality restriction. The
source-to-dictionary association remains exactly DeployedWrapper557. -/
theorem source_cone_reference557 (base : ExternalTypes)
    (p : Public base) (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
    (point : Array aspis_core.field.QM31 10#usize)
    (challenges : aspis_core.state_only_prefix.r0.Challenges) :
    PV_B3P_Install227.transport
      (source_continuation base (composed_ports557 base) p claims point challenges) =
      transported_reference base p claims point challenges := by
  rw [composed_ports_eq557]
  exact continuation_composes base _ (semantic_source_binding13 base)
    source_selection_binding13
    (parts_link13 _ _ local_links557.link6 local_links557.link7) p claims point challenges

/-- Exact remaining dictionary obligation, expanded through the composed
interpreter. This equivalence removes no native/source premise. -/
theorem deployed_wrapper_iff557 (base : ExternalTypes)
    (ops : @ExternalFuns (PV_B3P_Install227.Types base)) :
    DeployedWrapper557 base ops ↔
      PV_B3P_Link_terminal_qm31 base ops (composed_ports557 base) := by
  rw [composed_ports_eq557]
  rfl

#print axioms composed_ports_eq557
#print axioms source_cone_reference557
#print axioms deployed_wrapper_iff557
end
end PV_B3P_Closure557227
