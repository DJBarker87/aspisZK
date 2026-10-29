import PV_B3P_HornerBodyBinding8227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
def horner_direct_loop8 {N : Usize} (values : Array aspis_core.field.QM31 N)
    (prepared : host_terminal_field.PreparedQm31Multiplier)
    (composition : aspis_core.field.QM31) (index : Usize) : Result aspis_core.field.QM31 :=
  loop (fun state : aspis_core.field.QM31 × Usize =>
    horner_direct_body8 values prepared state.1 state.2) (composition,index)

attribute [local irreducible] horner_direct_body8

theorem horner_semantic_loop_binding8 (values : Array aspis_core.field.QM31 24#usize)
    (prepared : host_terminal_field.PreparedQm31Multiplier)
    (composition : aspis_core.field.QM31) (index : Usize) :
    reference_terminal.composition_parts_loop1 values prepared composition index =
      horner_direct_loop8 values prepared composition index := by
  unfold reference_terminal.composition_parts_loop1 horner_direct_loop8
  apply congrArg (fun body => loop body (composition,index))
  funext state
  exact horner_semantic_body_binding8 values prepared state.1 state.2
#print axioms horner_semantic_loop_binding8

theorem horner_poseidon_loop_binding8 (values : Array aspis_core.field.QM31 4#usize)
    (prepared : host_terminal_field.PreparedQm31Multiplier)
    (composition : aspis_core.field.QM31) (index : Usize) :
    reference_terminal.composition_parts_loop2 values prepared composition index =
      horner_direct_loop8 values prepared composition index := by
  unfold reference_terminal.composition_parts_loop2 horner_direct_loop8
  apply congrArg (fun body => loop body (composition,index))
  funext state
  exact horner_poseidon_body_binding8 values prepared state.1 state.2
#print axioms horner_poseidon_loop_binding8

end PV_B3P_Success227
