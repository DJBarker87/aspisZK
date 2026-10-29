import PV_B3P_ScaleLoop11227
namespace PV_B3P_Binding11227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false
theorem scale_loop_frame11 (selector : aspis_core.field.QM31) (range : ScaleRange11) :
    loop (usize_body scale_frame11 33#usize) ((selector,range),0#usize) = (do
      let next ← loop (usize_body (scale_cell11 selector) 33#usize) (range,0#usize)
      .ok (selector,next)) := by
  rw [loop_as_fold11 scale_frame11 33#usize 0#usize 33 (selector,range) (Eq.refl _)]
  rw [loop_as_fold11 (scale_cell11 selector) 33#usize 0#usize 33 range (Eq.refl _)]
  exact scale_frame_fold11 _ selector range
#print axioms scale_loop_frame11
end PV_B3P_Binding11227
