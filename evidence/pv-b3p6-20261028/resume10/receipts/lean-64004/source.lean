import PV_B3P_ValueRead911227
import PV_B3P_DigestCpsEq9227
import PV_B3P_ValueTail1012227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 Result ControlFlow Error
set_option autoImplicit false

def value_source_tail10_11 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result (Array aspis_core.field.QM31 24#usize) := do
  let q144 ← reference_terminal.read227 state.2 18#usize
  let q145 ← aspis_core.field.QM31.mul state.1 q144
  let range52 ← Array.update state.2 18#usize q145
  let q146 ← reference_terminal.read227 range52 19#usize
  let q147 ← aspis_core.field.QM31.mul state.1 q146
  let range53 ← Array.update range52 19#usize q147
  let q148 ← reference_terminal.read227 range53 20#usize
  let q149 ← aspis_core.field.QM31.mul state.1 q148
  let range54 ← Array.update range53 20#usize q149
  let q150 ← reference_terminal.read227 range54 21#usize
  let q151 ← aspis_core.field.QM31.mul state.1 q150
  let range55 ← Array.update range54 21#usize q151
  let q152 ← reference_terminal.read227 range55 22#usize
  let q153 ← aspis_core.field.QM31.mul state.1 q152
  let range56 ← Array.update range55 22#usize q153
  let q154 ← reference_terminal.read227 range56 23#usize
  let q155 ← aspis_core.field.QM31.mul state.1 q154
  let range57 ← Array.update range56 23#usize q155
  let q156 ← reference_terminal.read227 range57 24#usize
  let q157 ← aspis_core.field.QM31.mul state.1 q156
  let range58 ← Array.update range57 24#usize q157
  let q158 ← reference_terminal.read227 range58 25#usize
  let q159 ← aspis_core.field.QM31.mul state.1 q158
  let range59 ← Array.update range58 25#usize q159
  let q160 ← reference_terminal.read227 range59 26#usize
  let q161 ← aspis_core.field.QM31.mul state.1 q160
  let range60 ← Array.update range59 26#usize q161
  let q162 ← reference_terminal.read227 range60 27#usize
  let q163 ← aspis_core.field.QM31.mul state.1 q162
  let range61 ← Array.update range60 27#usize q163
  let q164 ← reference_terminal.read227 range61 28#usize
  let q165 ← aspis_core.field.QM31.mul state.1 q164
  let range62 ← Array.update range61 28#usize q165
  let q166 ← reference_terminal.read227 range62 29#usize
  let q167 ← aspis_core.field.QM31.mul state.1 q166
  let range63 ← Array.update range62 29#usize q167
  let q168 ← reference_terminal.read227 range63 30#usize
  let q169 ← aspis_core.field.QM31.mul state.1 q168
  let range64 ← Array.update range63 30#usize q169
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

attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.sub aspis_core.field.QM31.square aspis_core.field.QM31.mul aspis_core.field.QM31.mul_m31 Array.index_usize Array.update reference_terminal.read227 reference_terminal.reconstruct_10 reference_terminal.add_preweighted reference_copy_terminal.Selectors.row value_source_tail10_12

theorem value_source_equation10_11 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) :
    value_source_tail10_11 packed openings selectors state =
      value_owned_stage9_11 packed openings selectors state >>= value_source_tail10_12 packed openings selectors := by
  unfold value_source_tail10_11 value_owned_stage9_11 value_read_context9_11
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
  apply bind_equal9
  intro head_9
  apply bind_equal9
  intro head_10
  apply bind_equal9
  intro head_11
  apply bind_equal9
  intro head_12
  apply bind_equal9
  intro head_13
  apply bind_equal9
  intro head_14
  apply bind_equal9
  intro head_15
  apply bind_equal9
  intro head_16
  apply bind_equal9
  intro head_17
  unfold value_source_tail10_12
  rfl

#print axioms value_source_equation10_11
end PV_B3P_Binding10227
