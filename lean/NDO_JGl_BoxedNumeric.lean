import RPv_FIx_SelectedMeaning
import NDO_JGl_TensorAll
import NDO_JGl_NumericCanonical
import NDO_JGl_ArrayIdentity
import RPv_FJa_BoxedCanonical
import RPv_FJa_ExpansionMeaning
import RPv_FJa_SlicesValue
import RPv_FIz_BoxedOrigins
import NDO_JFy_PointCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGl_BoxedNumeric
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (decode)
open FIw_ArrayValue (canonical decoded)

theorem value (s : pool_v1.pair_forest_copy_terminal.Selectors)
    (run : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point JFu_TerminalPrefix.alpha=ok s) :
    s=JGl_NumericData.selectors := by
  obtain ⟨hi,lo,rhi,rhigh,rlo,rlow⟩ := FIz_BoxedOrigins.value JFu_TerminalPrefix.alpha s run
  have hp := JFy_PointCanonical.source
  have hv := FJa_SlicesValue.high JFu_TerminalPrefix.alpha hi rhi
  have lv := FJa_SlicesValue.low JFu_TerminalPrefix.alpha lo rlo
  have cs := FJa_BoxedCanonical.value JFu_TerminalPrefix.alpha s hp run
  have hh : decoded s.high=decoded JGl_NumericData.high := by
    funext j
    have h := FJa_ExpansionMeaning.value 64#usize hi s.high
      (FJa_SliceBounds.high _ _ hp rhi) (by rw [hv.2];decide) rhigh j
    have view : FIv_NativeArray.value s.high j.val=decoded s.high j :=
      FIx_SelectedMeaning.read s.high j.val j.isLt
    rw [view,hv.1] at h
    exact h.trans (JGl_TensorAll.high j)
  have hl : decoded s.low=decoded JGl_NumericData.low := by
    funext j
    have h := FJa_ExpansionMeaning.value 16#usize lo s.low
      (FJa_SliceBounds.low _ _ hp rlo) (by rw [lv.2];decide) rlow j
    have view : FIv_NativeArray.value s.low j.val=decoded s.low j :=
      FIx_SelectedMeaning.read s.low j.val j.isLt
    rw [view,lv.1] at h
    exact h.trans (JGl_TensorAll.low j)
  have eh := JGl_ArrayIdentity.value s.high JGl_NumericData.high cs.1 JGl_NumericCanonical.high hh
  have el := JGl_ArrayIdentity.value s.low JGl_NumericData.low cs.2 JGl_NumericCanonical.low hl
  cases s
  cases eh
  cases el
  rfl
#print axioms value
end AspisR1.JGl_BoxedNumeric
end
