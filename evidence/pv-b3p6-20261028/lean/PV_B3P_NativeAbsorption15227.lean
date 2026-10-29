import PV_B3P_AbsorptionCell15_00227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227 Result
set_option autoImplicit false

def native_absorption15 (low fixed chunk_two chunk_eight nodes : aspis_core.field.QM31) (openings : Array aspis_core.field.QM31 16#usize) : Result (Array aspis_core.field.QM31 16#usize) :=
  range_loop13 (absorption_step15 low fixed chunk_two chunk_eight nodes openings) 0#usize 16#usize
    (Array.repeat 16#usize aspis_core.field.QM31.ZERO)

theorem native_absorption_binding15 (low fixed chunk_two chunk_eight nodes : aspis_core.field.QM31) (openings : Array aspis_core.field.QM31 16#usize) :
    native_absorption15 low fixed chunk_two chunk_eight nodes openings = reference_terminal.absorption_lanes_literal low fixed chunk_two chunk_eight nodes openings := by
  unfold native_absorption15
  rw [range_sixteen13]
  exact (absorption_fold15_00 low fixed chunk_two chunk_eight nodes openings _).symm
#print axioms native_absorption_binding15
end PV_B3P_Native15227
