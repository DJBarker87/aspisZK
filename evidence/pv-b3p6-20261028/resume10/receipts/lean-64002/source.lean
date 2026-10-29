import PV_B3P_ValueRead913227
import PV_B3P_DigestCpsEq9227
import PV_B3P_ValueTail1014227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 Result ControlFlow Error
set_option autoImplicit false

def value_source_tail10_13 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result (Array aspis_core.field.QM31 24#usize) := do
  let q168 ← reference_terminal.read227 state.2 30#usize
  let q169 ← aspis_core.field.QM31.mul state.1 q168
  let range64 ← Array.update state.2 30#usize q169
  let q170 ← reference_terminal.read227 range64 31#usize
  let q171 ← aspis_core.field.QM31.mul state.1 q170
  let range65 ← Array.update range64 31#usize q171
  let q172 ← reference_terminal.read227 range65 32#usize
  let q173 ← aspis_core.field.QM31.mul state.1 q172
  let range66 ← Array.update range65 32#usize q173
  let packed1 ← reference_terminal.add_preweighted packed 49#usize range66
  let i27 ←
    lift (Std.Usize.wrapping_mul 16#usize
      reference_terminal.VALUE_AUXILIARY_BLOCK)
  let i28 ← lift (Std.Usize.wrapping_add i27 6#usize)
  let conservation_selector ←
    reference_copy_terminal.Selectors.row selectors i28
  let q174 ← Array.index_usize openings.z 0#usize
  let q175 ← Array.index_usize openings.z 1#usize
  let q176 ← aspis_core.field.QM31.sub q174 q175
  let q177 ← Array.index_usize openings.z 2#usize
  let q178 ← aspis_core.field.QM31.sub q176 q177
  let q179 ← aspis_core.field.QM31.mul conservation_selector q178
  let q180 ← Array.index_usize openings.succ_z 0#usize
  let q181 ← Array.index_usize openings.succ_z 1#usize
  let q182 ← aspis_core.field.QM31.sub q180 q181
  let q183 ← aspis_core.field.QM31.mul conservation_selector q182
  reference_terminal.add_preweighted packed1 82#usize
    (Array.make 2#usize [ q179, q183 ] (by simp only [List.length_cons,List.length_nil]; rfl))

attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.sub aspis_core.field.QM31.square aspis_core.field.QM31.mul aspis_core.field.QM31.mul_m31 Array.index_usize Array.update reference_terminal.read227 reference_terminal.reconstruct_10 reference_terminal.add_preweighted reference_copy_terminal.Selectors.row value_source_tail10_14

theorem value_source_equation10_13 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) :
    value_source_tail10_13 packed openings selectors state =
      value_owned_stage9_13 packed openings selectors state >>= value_source_tail10_14 packed openings selectors := by
  unfold value_source_tail10_13 value_owned_stage9_13 value_read_context9_13
  simp only [bind_assoc, bind_tc_ok]
  apply bind_equal9
  intro head_0
  apply bind_equal9
  intro head_1
  apply bind_equal9
  intro head_2
  apply bind_equal9
  intro head_3
  apply bind_equal9
  intro head_4
  apply bind_equal9
  intro head_5
  apply bind_equal9
  intro head_6
  apply bind_equal9
  intro head_7
  apply bind_equal9
  intro head_8
  unfold value_source_tail10_14
  rfl

#print axioms value_source_equation10_13
end PV_B3P_Binding10227
