import PV_B3P_CopyActiveLoop12227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding10227 PV_B3P_Binding11227 PV_B3P_Binding12227 PV_B3P_Binding13227 Result
set_option autoImplicit false

def native_active15 (selectors : reference_copy_terminal.Selectors) : Result aspis_core.field.QM31 :=
  loop (usize_body (active_step12 selectors) 64#usize) (aspis_core.field.QM31.ZERO,0#usize)

theorem native_active_binding15 (selectors : reference_copy_terminal.Selectors) :
    native_active15 selectors = reference_copy_terminal.Selectors.active_literal selectors := by
  change _ = reference_copy_terminal.Selectors.active_literal_loop selectors _ _
  exact (active_loop_binding12 selectors _ _).symm
#print axioms native_active_binding15
end PV_B3P_Native15227
