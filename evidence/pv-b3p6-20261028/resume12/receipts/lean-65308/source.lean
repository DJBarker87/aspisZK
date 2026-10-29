import PV_B3P_P227_08
import PV_B3P_Ordered227
import PV_B3P_DigestCpsEq9227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 Result
set_option autoImplicit false

abbrev LeadingState12 := Array aspis_core.field.QM31 16#usize
def leading_step12 (xor_values : LeadingState12) (state : LeadingState12) (index : Usize) : Result LeadingState12 := do
  let left ← Array.index_usize state index
  let right ← Array.index_usize xor_values index
  let value ← aspis_core.field.QM31.add left right
  Array.update state index value

def leading_finish12 (state : LeadingState12) : Result (Array aspis_core.field.QM31 4#usize) := do
  let state8 ← reference_poseidon.external_linear_lazy state
  let a ← Array.index_usize reference_poseidon.EXTERNAL_INITIAL 0#usize
  let a1 ← reference_poseidon.full_round_m31_constants state8 a
  let a2 ← Array.index_usize reference_poseidon.EXTERNAL_INITIAL 1#usize
  reference_poseidon.full_round_m31_constants_packed a1 a2
end PV_B3P_Binding12227
