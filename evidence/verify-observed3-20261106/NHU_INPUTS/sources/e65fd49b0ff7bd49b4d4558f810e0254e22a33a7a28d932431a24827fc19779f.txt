import NHG_COMBINED_IMPORT
import NDO_JFy_Selectors
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.NHU_SelectorPacket
open FIq_Native
open pool_v1.pair_forest_copy_terminal
/-- Complete pure emitted construction on arbitrary canonical point10.
This does not interpret a native allocation or discharge the parent bridge. -/
theorem at_point (point : Array field.QM31 10#usize) (canonical : FIw_ArrayValue.canonical point) :
 ∃ s,Selectors.at_point point=ok s ∧ FIw_ArrayValue.canonical s.high ∧ FIw_ArrayValue.canonical s.low := by
 simpa only [Selectors.boxed_at_point] using JFy_Selectors.source point canonical

theorem boxed (point : Array field.QM31 10#usize) (canonical : FIw_ArrayValue.canonical point) :
 ∃ s,Selectors.boxed_at_point point=ok s ∧ FIw_ArrayValue.canonical s.high ∧ FIw_ArrayValue.canonical s.low :=
 JFy_Selectors.source point canonical
#print axioms at_point
#print axioms boxed
end AspisR1.NHU_SelectorPacket
end
