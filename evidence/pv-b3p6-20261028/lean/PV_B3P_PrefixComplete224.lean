import PV_B3P_PrefixLoop224
namespace PV_B3P_PrefixComplete224
open Aeneas Aeneas.Std PV_B3P_224Prefix PV_B3P_PrefixAction224
set_option autoImplicit false

def empty : aspis_statement.logup.CopyLogUpRow :=
  {producer_values := Array.repeat 2#usize aspis_core.field.QM31.ZERO
   producer_weights := Array.repeat 2#usize aspis_core.field.M31.ZERO
   consumer_values := Array.repeat 2#usize aspis_core.field.QM31.ZERO
   consumer_weights := Array.repeat 2#usize aspis_core.field.M31.ZERO}
def seed : Rows := Array.repeat 1024#usize empty

theorem complete_result (view : prefix224.View) (registry : Registry) (append_index : U64)
    (lambda : aspis_core.field.QM31) :
    prefix224.copy_rows view registry append_index lambda =
      PV_B3P_HelperState224.run (action view registry append_index lambda) 0 136 seed := by
  unfold prefix224.copy_rows
  rw [PV_B3P_PrefixLoop224.complete_loop view registry append_index lambda 136 _ 0#usize (by simp)]
  rfl

#print axioms complete_result
end PV_B3P_PrefixComplete224
