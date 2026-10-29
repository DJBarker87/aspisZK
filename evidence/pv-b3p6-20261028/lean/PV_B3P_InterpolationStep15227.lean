import PV_B3P_Operations12227
import PV_B3P_RangeFold13227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227 Result
set_option autoImplicit false

def interpolation_step15 (weights : Array aspis_core.field.QM31 3#usize) (column0 column1 column2 : Array U32 16#usize) (state : Array aspis_core.field.QM31 16#usize) (lane : Usize) :
    Result (Array aspis_core.field.QM31 16#usize) := do
  let c0 ← Array.index_usize column0 lane
  let c1 ← Array.index_usize column1 lane
  let c2 ← Array.index_usize column2 lane
  let value ← reference_poseidon.interpolate_column227 weights c0 c1 c2
  Array.update state lane value
end PV_B3P_Native15227
