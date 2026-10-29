import PV_B3P_Install227
import PV_B3P_RootLaw227
import PV_B3P_SelectD227
namespace PV_B3P_RootD227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_SelectIndex227 PV_B3P_SelectD227
set_option autoImplicit false

theorem complete_D (public1 : reference_terminal.SemanticPublic)
    (a b : Claims) (point : Array aspis_core.field.QM31 10#usize)
    (c : aspis_core.state_only_prefix.r0.Challenges)
    (h : ∀ r column,column.val<28 → view a r column=view b r column) :
    reference_terminal.reference227 public1 a point c =
      reference_terminal.reference227 public1 b point c := by
  unfold reference_terminal.reference227
  rw [source_D a b h]

#print axioms complete_D
end PV_B3P_RootD227

namespace PV_B3P_Resume5Combined
open Aeneas Aeneas.Std ProverRwFull
set_option autoImplicit false
noncomputable section
abbrev Types := PV_B3P_Carrier227.Types

theorem installed_complete (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (p : @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public (Types base))
    (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
    (point : Array aspis_core.field.QM31 10#usize)
    (c : aspis_core.state_only_prefix.r0.Challenges) :
    @ExternalFuns.op227 (Types base) (PV_B3P_Install227.actual base ops) p claims point c =
      PV_B3P_Install227.transport (PV_B3P_RootLaw227.plan
        (PV_B3P_Carrier227.semantic base p)
        (PV_B3P_Carrier227.mapArray (PV_B3P_Carrier227.mapArray PV_B3P_Carrier227.toQ) claims)
        (PV_B3P_Carrier227.mapArray PV_B3P_Carrier227.toQ point)
        (PV_B3P_Carrier227.challenges c)) := by
  rw [PV_B3P_Install227.actual_source,PV_B3P_RootLaw227.complete_result]

-- Supporting bridge only: no deployed native equality or successful nonvacuity
-- is inferred from the closed emitted composition/equality definitions in plan.
#print axioms installed_complete
#print axioms PV_B3P_RootD227.complete_D
end
end PV_B3P_Resume5Combined
