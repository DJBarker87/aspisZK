import PV_B3P_P227_10
import PV_B3P_Ordered227
import PV_B3P_DigitLoop10227
namespace PV_B3P_Binding11227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

def digest_store_cell11 (selector : aspis_core.field.QM31)
    (opened : Array aspis_core.field.QM31 16#usize) (start : Usize)
    (expected : Array aspis_core.field.M31 8#usize) (right_tweak : Bool)
    (output : Array aspis_core.field.QM31 8#usize) (lane : Usize) : Result (Array aspis_core.field.QM31 8#usize) := do
  let target0 ← Array.index_usize expected lane
  let target ← reference_terminal.tweak227 target0 right_tweak lane
  let previous ← Array.index_usize output lane
  let source ← lift (Usize.wrapping_add start lane)
  let opened_value ← Array.index_usize opened source
  let lifted ← reference_terminal.lift_m31 target
  let residual ← aspis_core.field.QM31.sub opened_value lifted
  let weighted ← aspis_core.field.QM31.mul selector residual
  let next ← aspis_core.field.QM31.add previous weighted
  Array.update output lane next

attribute [local irreducible] reference_terminal.tweak227 reference_terminal.lift_m31 Array.index_usize Array.update aspis_core.field.QM31.sub aspis_core.field.QM31.mul aspis_core.field.QM31.add Usize.wrapping_add

theorem digest_store_fold11 (output : Array aspis_core.field.QM31 8#usize)
    (selector : aspis_core.field.QM31) (opened : Array aspis_core.field.QM31 16#usize)
    (start : Usize) (expected : Array aspis_core.field.M31 8#usize) (right_tweak : Bool) :
    reference_terminal.add_digest_binding output selector opened start expected right_tweak =
      PV_B3P_Ordered227.fold (digest_store_cell11 selector opened start expected right_tweak)
        [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize] output := by
  simp only [reference_terminal.add_digest_binding,PV_B3P_Ordered227.fold,digest_store_cell11,PV_B3P_Ordered227.bind_assoc,bind_tc_ok,result_right]
#print axioms digest_store_fold11
end PV_B3P_Binding11227
