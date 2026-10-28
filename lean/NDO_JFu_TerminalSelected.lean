import NDO_JFu_BoundedBuilder
import NDO_JFu_TerminalCallback
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFu_TerminalSelected
open Aeneas Aeneas.Std Result FIq_Native

theorem source : ∃ out,array_from_fn_copy 84#usize field.QM31.Insts.CoreMarkerCopy
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
    field.QM31.ZERO JFu_TerminalCallback.claims=ok out := by
  unfold array_from_fn_copy
  apply JFu_BoundedBuilder.source
  exact JFu_TerminalCallback.source

#print axioms source
end AspisR1.JFu_TerminalSelected
end
