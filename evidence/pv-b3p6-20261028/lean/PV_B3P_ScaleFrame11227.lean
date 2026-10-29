import PV_B3P_ValueReadTypes9227
import PV_B3P_Ordered227
import PV_B3P_DigestCpsEq9227
namespace PV_B3P_Binding11227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

abbrev ScaleRange11 := Array aspis_core.field.QM31 33#usize
def scale_cell11 (selector : aspis_core.field.QM31) (range : ScaleRange11) (index : Usize) : Result ScaleRange11 := do
  let original ← Array.index_usize range index
  let scaled ← aspis_core.field.QM31.mul selector original
  Array.update range index scaled

def scale_frame11 (state : ValueState9) (index : Usize) : Result ValueState9 := do
  let next ← scale_cell11 state.1 state.2 index
  .ok (state.1,next)

/-- The scalar is a frame, while every successful write is threaded forward. -/
theorem scale_frame_fold11 (indices : List Usize) (selector : aspis_core.field.QM31) (range : ScaleRange11) :
    PV_B3P_Ordered227.fold scale_frame11 indices (selector,range) = (do
      let next ← PV_B3P_Ordered227.fold (scale_cell11 selector) indices range
      .ok (selector,next)) := by
  induction indices generalizing range with
  | nil => exact Eq.refl _
  | cons index rest ih =>
    simp only [PV_B3P_Ordered227.fold,scale_frame11,PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
    apply bind_equal9
    intro next
    exact ih next
#print axioms scale_frame_fold11
end PV_B3P_Binding11227
