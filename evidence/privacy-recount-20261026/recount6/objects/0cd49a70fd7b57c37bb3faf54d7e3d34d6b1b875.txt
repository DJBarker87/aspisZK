import PV_B1_PoleOriginal
set_option autoImplicit false
namespace PV_B1_Orig258_Op258End
open Aeneas Aeneas.Std Result ControlFlow PV_B1_258

theorem body_done
    (values : Slice (Array (Array aspis_core.field.QM31 2#usize) 2#usize))
    (masks : Array U16 64#usize) (chi : aspis_core.field.QM31)
    (clear : Bool) (row : Usize) (h : ¬ row < Slice.len values) :
    PV_B1_PoleOriginal.reference.all_slots_clear_loop.body values masks chi clear row =
      ok (done clear) := by
  simp only [PV_B1_PoleOriginal.reference.all_slots_clear_loop.body,if_neg h]
#print axioms body_done
end PV_B1_Orig258_Op258End
