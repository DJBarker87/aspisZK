import R1Z.PV_CB3_Op258Ref
set_option autoImplicit false
namespace R1Z.PV_CB3_Op258End
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull

theorem body_done
    (values : Slice (Array (Array aspis_core.field.QM31 2#usize) 2#usize))
    (masks : Array U16 64#usize) (chi : aspis_core.field.QM31)
    (clear : Bool) (row : Usize) (h : ¬ row < Slice.len values) :
    PV_CB3_Op258Ref.reference.all_slots_clear_loop.body values masks chi clear row =
      ok (done clear) := by
  simp only [PV_CB3_Op258Ref.reference.all_slots_clear_loop.body,if_neg h]
#print axioms body_done
end R1Z.PV_CB3_Op258End
