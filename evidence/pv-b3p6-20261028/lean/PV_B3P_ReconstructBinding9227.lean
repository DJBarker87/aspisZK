import PV_B3P_NineUnroll9227
import PV_B3P_P227_08
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Ordered227
set_option autoImplicit false

def reconstruct_step (view : Array aspis_core.field.QM31 16#usize)
    (acc : aspis_core.field.QM31) (i : Usize) : Result aspis_core.field.QM31 := do
  let doubled ← aspis_core.field.QM31.add acc acc
  let value ← Array.index_usize view i
  aspis_core.field.QM31.add doubled value

def source_reconstruct (view : Array aspis_core.field.QM31 16#usize) :
    Result aspis_core.field.QM31 := do
  let acc ← Array.index_usize view 9#usize
  loop (reverse_body (reconstruct_step view)) (acc,9#usize)

attribute [local irreducible] aspis_core.field.QM31.add Array.index_usize

theorem reconstruct_loop_binding (view : Array aspis_core.field.QM31 16#usize)
    (acc : aspis_core.field.QM31) :
    loop (reverse_body (reconstruct_step view)) (acc,9#usize) =
      reverse_plan (reconstruct_step view) 9 9#usize acc :=
  reverse_loop_plan (reconstruct_step view) 9#usize 9 acc rfl

theorem reconstruct_entry_factor (view : Array aspis_core.field.QM31 16#usize) :
    reference_terminal.reconstruct_10 view = (do
      let acc ← Array.index_usize view 9#usize
      reverse_plan (reconstruct_step view) 9 9#usize acc) := by
  simp only [reverse_nine,reconstruct_step,bind_assoc,reference_terminal.reconstruct_10]

theorem reconstruct_body_binding (view : Array aspis_core.field.QM31 16#usize) :
    source_reconstruct view = reference_terminal.reconstruct_10 view := by
  unfold source_reconstruct
  simp only [reconstruct_loop_binding]
  exact (reconstruct_entry_factor view).symm

#print axioms reconstruct_loop_binding
#print axioms reconstruct_entry_factor
#print axioms reconstruct_body_binding
end PV_B3P_Binding9227
