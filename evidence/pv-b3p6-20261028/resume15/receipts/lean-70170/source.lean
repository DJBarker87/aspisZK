import PV_B3P_Operations12227
import PV_B3P_RangeFold13227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227 Result
set_option autoImplicit false

def absorption_step15 (low fixed chunk_two chunk_eight nodes : aspis_core.field.QM31) (openings : Array aspis_core.field.QM31 16#usize) (state : Array aspis_core.field.QM31 16#usize) (lane : Usize) :
    Result (Array aspis_core.field.QM31 16#usize) := do
  let opened ← reference_terminal.read227 openings lane
  let value ← reference_terminal.absorption_lane227 lane low fixed chunk_two chunk_eight nodes opened
  Array.update state lane value
end PV_B3P_Native15227
