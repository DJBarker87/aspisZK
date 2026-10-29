import PV_B3P_NativeLeading15227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding10227 PV_B3P_Binding11227 PV_B3P_Binding12227 PV_B3P_Binding13227 Result
set_option autoImplicit false

def native_digest_store15 (output : Array aspis_core.field.QM31 8#usize)
    (selector : aspis_core.field.QM31) (opened : Array aspis_core.field.QM31 16#usize)
    (start : Usize) (expected : Array aspis_core.field.M31 8#usize) (right_tweak : Bool) :
    Result (Array aspis_core.field.QM31 8#usize) :=
  range_loop13 (digest_store_cell11 selector opened start expected right_tweak) 0#usize 8#usize output

theorem native_digest_store_binding15 (output : Array aspis_core.field.QM31 8#usize)
    (selector : aspis_core.field.QM31) (opened : Array aspis_core.field.QM31 16#usize)
    (start : Usize) (expected : Array aspis_core.field.M31 8#usize) (right_tweak : Bool) :
    native_digest_store15 output selector opened start expected right_tweak =
      reference_terminal.add_digest_binding output selector opened start expected right_tweak := by
  unfold native_digest_store15
  rw [range_as_fold13 _ 0#usize 8#usize 8 _ (by rfl),leading_indices15]
  exact (digest_store_fold11 output selector opened start expected right_tweak).symm
#print axioms native_digest_store_binding15
end PV_B3P_Native15227
