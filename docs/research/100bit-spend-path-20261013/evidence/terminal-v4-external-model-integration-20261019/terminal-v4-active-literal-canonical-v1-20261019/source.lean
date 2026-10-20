import TerminalV4ActiveLiteralClosureV2
import TerminalV4TowerAddV2
import TerminalV4QM31MulCurrent
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1.TerminalV4ActiveLiteralCanonical
abbrev QM := AspisR1SelectedMaskProbe.field.QM31
abbrev CanonicalQM := AspisR1.TerminalV4TowerAdd.CanonicalQM
abbrev Values := Array QM 16#usize

def valueCell (values : Values) (i : Fin 16) : QM :=
  values.val[i.val]'(by simpa [values.property] using i.isLt)

theorem sum_6144_success_canonical (values : Values) (out : QM)
    (hvalues : ∀ i : Fin 16, CanonicalQM (valueCell values i))
    (hrun : AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.selector_mask_sum_16
      values 6144#u16 = .ok out) :
    CanonicalQM out := by
  have h := hrun
  simp only [AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.selector_mask_sum_16,
    core.num.U16.count_ones, core.num.U16.count_ones_nat,
    core.num.U16.count_ones_aux] at h
  trace_state
  exact False.elim (by assumption)
end AspisR1.TerminalV4ActiveLiteralCanonical
