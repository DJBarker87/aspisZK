import AspisR1.TerminalV4ActiveLiteralLoopCanonical
open Aeneas Aeneas.Std Result ControlFlow Error WP
set_option autoImplicit false
namespace AspisR1.TerminalV4ActiveLiteralCanonicalFromInputs
abbrev QM := AspisR1SelectedMaskProbe.field.QM31
abbrev Canonical := AspisR1.TerminalV4TowerAdd.CanonicalQM
abbrev Selectors := AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.Selectors
abbrev ActiveLiteral := AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.Selectors.active_literal
abbrev ActiveLoop := AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.Selectors.active_literal_loop

theorem active_literal_success_canonical (s : Selectors) (out : QM)
    (hhigh : ∀ i : Fin 64, Canonical (AspisR1.TerminalV4ActiveLiteralLoopCanonical.highCell s i))
    (hlow : ∀ i : Fin 16, Canonical (AspisR1.TerminalV4ActiveLiteralLoopCanonical.lowCell s i))
    (hrun : ActiveLiteral s = .ok out) : Canonical out := by
  have hsum : Canonical AspisR1SelectedMaskProbe.field.QM31.ZERO :=
    AspisR1.TerminalV4SelectorMaskSumCanonical.zero_one_canonical.1
  have hrun' : ActiveLoop s AspisR1SelectedMaskProbe.field.QM31.ZERO 0#usize = .ok out := by
    change ActiveLoop s AspisR1SelectedMaskProbe.field.QM31.ZERO 0#usize = .ok out
    exact hrun
  exact AspisR1.TerminalV4ActiveLiteralLoopCanonical.active_loop_good
    64 s 0#usize AspisR1SelectedMaskProbe.field.QM31.ZERO out
    (by scalar_tac) hsum hhigh hlow hrun'
end AspisR1.TerminalV4ActiveLiteralCanonicalFromInputs
