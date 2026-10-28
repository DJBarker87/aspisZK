import NDO_JGn_ActiveMath
import RPv_JGa_ActiveLoop
import NDO_JGl_NumericCanonical
import NDO_JGb_DecodeInjective
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_ActiveNumeric
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon decode)
open pool_v1.pair_forest_copy_terminal

theorem canonical : Canon JGn_ActiveData.a64 := by
  change (766140686<2147483647 ∧ 1850622266<2147483647) ∧ (1931269867<2147483647 ∧ 1348309306<2147483647)
  omega
#print axioms canonical

theorem source : Selectors.active JGl_NumericData.selectors=ok JGn_ActiveData.a64 := by
  obtain ⟨out,run,hc⟩ := WP.spec_imp_exists (JGa_ActiveLoop.full JGl_NumericData.selectors
    JGl_NumericCanonical.high JGl_NumericCanonical.low)
  have called : Selectors.active_literal_loop JGl_NumericData.selectors field.QM31.ZERO 0#usize=ok out := run
  have v := FJk_ActiveValue.loop 64 0#usize JGl_NumericData.selectors field.QM31.ZERO out rfl
    JGl_NumericCanonical.high JGl_NumericCanonical.low FIv_NativeValue.zero.1 called
  have value : decode out=FJk_ActiveValue.model JGl_NumericData.selectors 0 0 := by
    simpa only [show (0#usize).val=0 from rfl,FIv_NativeValue.zero.2] using v.2
  have same := JGb_DecodeInjective.source out JGn_ActiveData.a64 hc canonical
    (value.trans JGn_ActiveMath.value)
  exact same ▸ run
#print axioms source
end AspisR1.JGn_ActiveNumeric
end
