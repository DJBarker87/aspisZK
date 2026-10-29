import PV_B3P_PreweightedBuild12227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 Result
set_option autoImplicit false

def preweighted_source_step12 {N : Usize} (start : Usize)
    (values : Array aspis_core.field.QM31 N)
    (packed : Array aspis_core.field.QM31 24#usize) (group_index : Usize) :
    Result (Array aspis_core.field.QM31 24#usize) := do
  let lanes ← four_build12 (preweighted_window12 start values group_index)
  let old ← Array.index_usize packed group_index
  let slice ← lift (Array.to_slice lanes)
  let value ← host_terminal_field.qm31_pack_base4 slice
  let next ← aspis_core.field.QM31.add old value
  Array.update packed group_index next

attribute [local irreducible] Array.index_usize Array.update host_terminal_field.qm31_pack_base4 aspis_core.field.QM31.add Usize.wrapping_add Usize.wrapping_mul Usize.wrapping_sub

theorem preweighted_step_binding12 {N : Usize} (start : Usize)
    (values : Array aspis_core.field.QM31 N) (last : Usize)
    (packed : Array aspis_core.field.QM31 24#usize) (group_index : Usize) :
    reference_terminal.add_preweighted_loop.body start values last packed group_index =
      (if group_index <= last then do
        let next ← preweighted_source_step12 start values packed group_index
        .ok (.cont (next,Usize.wrapping_add group_index 1#usize))
      else .ok (.done packed)) := by
  unfold preweighted_source_step12
  rw [← preweighted_build_binding12]
  simp only [reference_terminal.add_preweighted_loop.body,preweighted_build_stores12,
    lift,bind_tc_ok,PV_B3P_Ordered227.bind_assoc,bind_branch12,bind_return12]

#print axioms preweighted_step_binding12
end PV_B3P_Binding12227
