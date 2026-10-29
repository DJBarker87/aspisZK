import PV_B3P_EqualityBinding9227
import PV_B3P_LinkDefinitions13227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false
/-- Exact Link definition, unchanged: the source loop model is the explicit
instance. Native source/array-index association remains separately audited. -/
theorem equality_link13 :
    PV_B3P_Links13227.PV_B3P_Link_terminal_equality_value source_equality_value :=
  funext (fun left => funext (equality_body_binding left))

/-- The actual loop guard specializes the fixed-array read law. -/
theorem equality_left_index13 (left : Array aspis_core.field.QM31 10#usize)
    (index : Usize) (guard : index < 10#usize) :
    ∃ value, Array.index_usize left index = .ok value := by
  have h : index.val < 10 := by scalar_tac
  exact ⟨_,PV_B3P_SelectIndex227.index_value left index h⟩

theorem equality_right_index13 (right : Array aspis_core.field.QM31 10#usize)
    (index : Usize) (guard : index < 10#usize) :
    ∃ value, Array.index_usize right index = .ok value := by
  have h : index.val < 10 := by scalar_tac
  exact ⟨_,PV_B3P_SelectIndex227.index_value right index h⟩

#print axioms equality_link13
#print axioms equality_left_index13
#print axioms equality_right_index13
end PV_B3P_Binding13227
