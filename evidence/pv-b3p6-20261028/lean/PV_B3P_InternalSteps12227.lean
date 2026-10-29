import PV_B3P_P227_06
import PV_B3P_DigestCpsEq9227
import PV_B3P_BindBranch12227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 Result
set_option autoImplicit false

abbrev InternalState12 := Array aspis_core.field.QM31 16#usize
abbrev InternalSum12 := Array U64 4#usize
def internal_sum_step12 (state : InternalState12) (sum : InternalSum12) (lane : Usize) : Result InternalSum12 := do
  let value ← Array.index_usize state lane
  reference_poseidon.internal_sum227 sum value
def internal_output_step12 (full_sum : InternalSum12) (state : InternalState12) (lane : Usize) : Result InternalState12 := do
  let value ← Array.index_usize state lane
  let offset ← lift (Usize.wrapping_sub lane 1#usize)
  let shift ← Array.index_usize reference_poseidon.internal_linear_lazy.SHIFTS offset
  let output ← reference_poseidon.internal_shift227 value full_sum shift
  Array.update state lane output
end PV_B3P_Binding12227
