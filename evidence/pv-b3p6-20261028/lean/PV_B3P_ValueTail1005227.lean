import PV_B3P_ValueRead905227
import PV_B3P_DigestCpsEq9227
import PV_B3P_ValueTail1006227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 Result ControlFlow Error
set_option autoImplicit false

def value_source_tail10_05 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result (Array aspis_core.field.QM31 24#usize) := do
  let q68 ← reference_terminal.read227 openings.xor12_z 0#usize
  let q69 ← aspis_core.field.QM31.square q68
  let q70 ← aspis_core.field.QM31.sub q69 q68
  let i15 ← lift (Std.Usize.wrapping_add 20#usize 0#usize)
  let range21 ← Array.update state.2 i15 q70
  let q71 ← reference_terminal.read227 openings.xor12_z 1#usize
  let q72 ← aspis_core.field.QM31.square q71
  let q73 ← aspis_core.field.QM31.sub q72 q71
  let i16 ← lift (Std.Usize.wrapping_add 20#usize 1#usize)
  let range22 ← Array.update range21 i16 q73
  let q74 ← reference_terminal.read227 openings.xor12_z 2#usize
  let q75 ← aspis_core.field.QM31.square q74
  let q76 ← aspis_core.field.QM31.sub q75 q74
  let i17 ← lift (Std.Usize.wrapping_add 20#usize 2#usize)
  let range23 ← Array.update range22 i17 q76
  let q77 ← reference_terminal.read227 openings.xor12_z 3#usize
  let q78 ← aspis_core.field.QM31.square q77
  let q79 ← aspis_core.field.QM31.sub q78 q77
  let i18 ← lift (Std.Usize.wrapping_add 20#usize 3#usize)
  let range24 ← Array.update range23 i18 q79
  let q80 ← reference_terminal.read227 openings.xor12_z 4#usize
  let q81 ← aspis_core.field.QM31.square q80
  let q82 ← aspis_core.field.QM31.sub q81 q80
  let i19 ← lift (Std.Usize.wrapping_add 20#usize 4#usize)
  let range25 ← Array.update range24 i19 q82
  let q83 ← reference_terminal.read227 openings.xor12_z 5#usize
  let q84 ← aspis_core.field.QM31.square q83
  let q85 ← aspis_core.field.QM31.sub q84 q83
  let i20 ← lift (Std.Usize.wrapping_add 20#usize 5#usize)
  let range26 ← Array.update range25 i20 q85
  let q86 ← reference_terminal.read227 openings.xor12_z 6#usize
  let q87 ← aspis_core.field.QM31.square q86
  let q88 ← aspis_core.field.QM31.sub q87 q86
  let i21 ← lift (Std.Usize.wrapping_add 20#usize 6#usize)
  let range27 ← Array.update range26 i21 q88
  let q89 ← reference_terminal.read227 openings.xor12_z 7#usize
  let q90 ← aspis_core.field.QM31.square q89
  let q91 ← aspis_core.field.QM31.sub q90 q89
  let i22 ← lift (Std.Usize.wrapping_add 20#usize 7#usize)
  let range28 ← Array.update range27 i22 q91
  let q92 ← reference_terminal.read227 openings.xor12_z 8#usize
  let q93 ← aspis_core.field.QM31.square q92
  let q94 ← aspis_core.field.QM31.sub q93 q92
  let i23 ← lift (Std.Usize.wrapping_add 20#usize 8#usize)
  let range29 ← Array.update range28 i23 q94
  let q95 ← reference_terminal.read227 openings.xor12_z 9#usize
  let q96 ← aspis_core.field.QM31.square q95
  let q97 ← aspis_core.field.QM31.sub q96 q95
  let i24 ← lift (Std.Usize.wrapping_add 20#usize 9#usize)
  let range30 ← Array.update range29 i24 q97
  let q98 ← reference_terminal.reconstruct_10 openings.z
  let q99 ← reference_terminal.reconstruct_10 openings.succ_z
  let i25 ← lift (Std.U32.wrapping_shl 1#u32 10#u32)
  let q100 ← aspis_core.field.QM31.mul_m31 q99 i25
  let q101 ← aspis_core.field.QM31.add q98 q100
  let q102 ← reference_terminal.reconstruct_10 openings.xor12_z
  let i26 ← lift (Std.U32.wrapping_shl 1#u32 20#u32)
  let q103 ← aspis_core.field.QM31.mul_m31 q102 i26
  let reconstructed ← aspis_core.field.QM31.add q101 q103
  let q104 ← Array.index_usize openings.z 10#usize
  let q105 ← aspis_core.field.QM31.sub q104 reconstructed
  let range31 ← Array.update range30 30#usize q105
  let q106 ← Array.index_usize openings.succ_z 10#usize
  let range32 ← Array.update range31 31#usize q106
  let q107 ← Array.index_usize openings.xor12_z 10#usize
  let range33 ← Array.update range32 32#usize q107
  let q108 ← reference_terminal.read227 range33 0#usize
  let q109 ← aspis_core.field.QM31.mul state.1 q108
  let range34 ← Array.update range33 0#usize q109
  let q110 ← reference_terminal.read227 range34 1#usize
  let q111 ← aspis_core.field.QM31.mul state.1 q110
  let range35 ← Array.update range34 1#usize q111
  let q112 ← reference_terminal.read227 range35 2#usize
  let q113 ← aspis_core.field.QM31.mul state.1 q112
  let range36 ← Array.update range35 2#usize q113
  let q114 ← reference_terminal.read227 range36 3#usize
  let q115 ← aspis_core.field.QM31.mul state.1 q114
  let range37 ← Array.update range36 3#usize q115
  let q116 ← reference_terminal.read227 range37 4#usize
  let q117 ← aspis_core.field.QM31.mul state.1 q116
  let range38 ← Array.update range37 4#usize q117
  let q118 ← reference_terminal.read227 range38 5#usize
  let q119 ← aspis_core.field.QM31.mul state.1 q118
  let range39 ← Array.update range38 5#usize q119
  let q120 ← reference_terminal.read227 range39 6#usize
  let q121 ← aspis_core.field.QM31.mul state.1 q120
  let range40 ← Array.update range39 6#usize q121
  let q122 ← reference_terminal.read227 range40 7#usize
  let q123 ← aspis_core.field.QM31.mul state.1 q122
  let range41 ← Array.update range40 7#usize q123
  let q124 ← reference_terminal.read227 range41 8#usize
  let q125 ← aspis_core.field.QM31.mul state.1 q124
  let range42 ← Array.update range41 8#usize q125
  let q126 ← reference_terminal.read227 range42 9#usize
  let q127 ← aspis_core.field.QM31.mul state.1 q126
  let range43 ← Array.update range42 9#usize q127
  let q128 ← reference_terminal.read227 range43 10#usize
  let q129 ← aspis_core.field.QM31.mul state.1 q128
  let range44 ← Array.update range43 10#usize q129
  let q130 ← reference_terminal.read227 range44 11#usize
  let q131 ← aspis_core.field.QM31.mul state.1 q130
  let range45 ← Array.update range44 11#usize q131
  let q132 ← reference_terminal.read227 range45 12#usize
  let q133 ← aspis_core.field.QM31.mul state.1 q132
  let range46 ← Array.update range45 12#usize q133
  let q134 ← reference_terminal.read227 range46 13#usize
  let q135 ← aspis_core.field.QM31.mul state.1 q134
  let range47 ← Array.update range46 13#usize q135
  let q136 ← reference_terminal.read227 range47 14#usize
  let q137 ← aspis_core.field.QM31.mul state.1 q136
  let range48 ← Array.update range47 14#usize q137
  let q138 ← reference_terminal.read227 range48 15#usize
  let q139 ← aspis_core.field.QM31.mul state.1 q138
  let range49 ← Array.update range48 15#usize q139
  let q140 ← reference_terminal.read227 range49 16#usize
  let q141 ← aspis_core.field.QM31.mul state.1 q140
  let range50 ← Array.update range49 16#usize q141
  let q142 ← reference_terminal.read227 range50 17#usize
  let q143 ← aspis_core.field.QM31.mul state.1 q142
  let range51 ← Array.update range50 17#usize q143
  let q144 ← reference_terminal.read227 range51 18#usize
  let q145 ← aspis_core.field.QM31.mul state.1 q144
  let range52 ← Array.update range51 18#usize q145
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

attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.sub aspis_core.field.QM31.square aspis_core.field.QM31.mul aspis_core.field.QM31.mul_m31 Array.index_usize Array.update reference_terminal.read227 reference_terminal.reconstruct_10 reference_terminal.add_preweighted reference_copy_terminal.Selectors.row value_source_tail10_06

theorem value_source_equation10_05 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) :
    value_source_tail10_05 packed openings selectors state =
      value_owned_stage9_05 packed openings selectors state >>= value_source_tail10_06 packed openings selectors := by
  unfold value_source_tail10_05 value_owned_stage9_05 value_read_context9_05
  conv_rhs => simp only [bind_assoc, bind_tc_ok]
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
  apply bind_equal9
  intro head_18
  apply bind_equal9
  intro head_19
  apply bind_equal9
  intro head_20
  apply bind_equal9
  intro head_21
  apply bind_equal9
  intro head_22
  apply bind_equal9
  intro head_23
  apply bind_equal9
  intro head_24
  unfold value_source_tail10_06
  rfl

#print axioms value_source_equation10_05
end PV_B3P_Binding10227
