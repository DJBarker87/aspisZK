import PV_B3P_HornerBodyBinding8227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

theorem read_function_binding :
    @reference_terminal.read227 =
      (fun {N : Usize} (values : Array aspis_core.field.QM31 N) (i : Usize) => Array.index_usize values i) := by
  funext N values i
  exact PV_B3P_Success227.read_helper_binding8 values i

theorem digest_function_binding :
    reference_terminal.digest227 =
      (fun (values : Array (Array U32 8#usize) 20#usize) (i : Usize) => Array.index_usize values i) := by
  funext values i
  exact PV_B3P_Success227.digest_helper_binding8 values i

#print axioms read_function_binding
#print axioms digest_function_binding
end PV_B3P_Binding9227
