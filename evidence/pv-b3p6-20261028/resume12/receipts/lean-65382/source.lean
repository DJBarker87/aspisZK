import PV_B3P_InternalOutput1201227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 Result
set_option autoImplicit false
def internal_finish12 (state : InternalState12) (old_zero : Array U32 4#usize) (part_sum : InternalSum12) : Result InternalState12 := do
  let full_sum ← reference_poseidon.internal_full_sum227 part_sum old_zero
  let q16 ← reference_poseidon.internal_zero227 part_sum old_zero
  let state1 ← Array.update state 0#usize q16
  internal_output_tail12_01 full_sum state1
end PV_B3P_Binding12227
