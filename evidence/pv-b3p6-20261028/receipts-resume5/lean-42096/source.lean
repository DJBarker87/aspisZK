import PV_B3P_P227_14
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
