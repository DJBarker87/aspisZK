import PV_B3P_NativeAbsorption15227
import PV_B3P_AbsorptionNativeRead15227
import PV_B3P_BoundedFold15227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227 Result
set_option autoImplicit false

def absorption_source_step15 (low fixed chunk_two chunk_eight nodes : aspis_core.field.QM31) (openings : Array aspis_core.field.QM31 16#usize) (state : Array aspis_core.field.QM31 16#usize) (lane : Usize) : Result (Array aspis_core.field.QM31 16#usize) := do
  let value ← absorption_native_value15 lane low fixed chunk_two chunk_eight nodes openings
  Array.update state lane value

theorem absorption_source_step_binding15 (low fixed chunk_two chunk_eight nodes : aspis_core.field.QM31) (openings : Array aspis_core.field.QM31 16#usize) (state : Array aspis_core.field.QM31 16#usize)
    (lane : Usize) (bound : lane.val < 16) :
    absorption_source_step15 low fixed chunk_two chunk_eight nodes openings state lane = absorption_step15 low fixed chunk_two chunk_eight nodes openings state lane := by
  unfold absorption_source_step15 absorption_step15
  rw [absorption_native_value_binding15 lane low fixed chunk_two chunk_eight nodes openings bound]
  simp only [PV_B3P_Ordered227.bind_assoc]

def absorption_source15 (low fixed chunk_two chunk_eight nodes : aspis_core.field.QM31) (openings : Array aspis_core.field.QM31 16#usize) : Result (Array aspis_core.field.QM31 16#usize) :=
  loop (usize_body (absorption_source_step15 low fixed chunk_two chunk_eight nodes openings) 16#usize)
    (Array.repeat 16#usize aspis_core.field.QM31.ZERO,0#usize)

theorem absorption_source_binding15 (low fixed chunk_two chunk_eight nodes : aspis_core.field.QM31) (openings : Array aspis_core.field.QM31 16#usize) :
    absorption_source15 low fixed chunk_two chunk_eight nodes openings = reference_terminal.absorption_lanes_literal low fixed chunk_two chunk_eight nodes openings := by
  rw [←native_absorption_binding15]
  unfold absorption_source15 native_absorption15
  rw [loop_as_fold11 _ 16#usize 0#usize 16 _ (by rfl),
    range_as_fold13 _ 0#usize 16#usize 16 _ (by rfl)]
  apply fold_pointwise15
  intro index member state
  exact absorption_source_step_binding15 low fixed chunk_two chunk_eight nodes openings state index (indices_bound_sixteen15 index member)
#print axioms absorption_source_step_binding15
#print axioms absorption_source_binding15
end PV_B3P_Native15227
