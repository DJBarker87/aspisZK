import PV_B3P_DirectPreweightedOperation17227
namespace PV_B3P_Direct17227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

/-- The eight plain-helper call shapes from the frozen host_terminal.rs.
The optimized shared-selector helper is a distinct function and not included. -/
def PreweightedActualCall17 (N start : Usize) : Prop :=
  (N = 16#usize ∧ start = 0#usize) ∨
  (N = 16#usize ∧ start = 16#usize) ∨
  (N = 17#usize ∧ start = 32#usize) ∨
  (N = 33#usize ∧ start = 49#usize) ∨
  (N = 2#usize ∧ start = 82#usize) ∨
  (N = 12#usize ∧ start = 0#usize) ∨
  (N = 8#usize ∧ start = 84#usize) ∨
  (N = 2#usize ∧ start = 92#usize)

theorem preweighted_actual_bounds17 (N start : Usize)
    (actual : PreweightedActualCall17 N start) :
    0 < N.val ∧ start.val+N.val ≤ 96 := by
  rcases actual with h|h|h|h|h|h|h|h <;>
    rcases h with ⟨rfl,rfl⟩ <;> decide

theorem preweighted_actual_extraction_reference17 {N : Usize}
    (packed : Array aspis_core.field.QM31 24#usize) (start : Usize)
    (values : Array aspis_core.field.QM31 N) (actual : PreweightedActualCall17 N start) :
    host_terminal.add_preweighted packed start values =
      reference_terminal.add_preweighted packed start values :=
  preweighted_extraction_reference17 packed start values
    (preweighted_actual_bounds17 N start actual).1
    (preweighted_actual_bounds17 N start actual).2
#print axioms preweighted_actual_bounds17
#print axioms preweighted_actual_extraction_reference17
end PV_B3P_Direct17227
