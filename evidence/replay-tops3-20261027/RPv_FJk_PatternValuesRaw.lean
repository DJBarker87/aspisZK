import RPv_FJk_PatternOuterValue
import RPv_FJk_CopyPowersValue
import RPv_JFy_ZeroArrays
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_PatternValuesRaw
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_copy_terminal
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
/-- Complete ORIGINAL pattern constructor VALUE, retaining the SAME powers array. -/
theorem value (a : Array field.QM31 16#usize) (lambda : field.QM31)
    (out : Array field.QM31 14#usize) (ha : canonical a) (hl : Canon lambda)
    (run : pattern_values a lambda=ok out) :
    ∃ powers : Array field.QM31 16#usize,
      canonical powers ∧ decoded powers=(fun i=>decode lambda^(i.val+1)) ∧
      canonical out ∧ decoded out=FJk_PatternOuterValue.model a powers := by
  unfold pattern_values pattern_values_literal at run
  obtain ⟨⟨powers,last⟩,rp,run⟩ := FIv_Map.bind_success _ _ _ run
  have p := FJk_CopyPowersValue.loop 16 0#usize lambda lambda _ powers last rfl hl hl
    (JFy_ZeroArrays.source 16#usize) (by rw [show (0#usize).val=0 from rfl,pow_one])
    (by intro j hj;have z : (0#usize).val=0 :=rfl;rw [z] at hj;omega) rp
  have o := FJk_PatternOuterValue.value 14 0#usize last a powers _ out rfl ha p.1
    (JFy_ZeroArrays.source 14#usize)
    (by intro j hj;have z : (0#usize).val=0 :=rfl;rw [z] at hj;omega) run
  exact ⟨powers,p.1,p.2.2,o.1,o.2⟩
#print axioms value
end AspisR1.FJk_PatternValuesRaw
end
