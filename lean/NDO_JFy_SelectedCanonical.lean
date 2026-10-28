import NDO_JFy_BoundedCanonical
import NDO_JFy_TerminalCallbackCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_SelectedCanonical
open Aeneas Aeneas.Std Result FIq_Native

theorem source : ∃ selected,
    array_from_fn_copy 84#usize field.QM31.Insts.CoreMarkerCopy
      pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      field.QM31.ZERO JFu_TerminalCallback.claims=ok selected ∧ FIw_ArrayValue.canonical selected := by
  unfold array_from_fn_copy
  apply JFy_BoundedCanonical.source
  exact JFy_TerminalCallbackCanonical.source
#print axioms source
end AspisR1.JFy_SelectedCanonical
end
