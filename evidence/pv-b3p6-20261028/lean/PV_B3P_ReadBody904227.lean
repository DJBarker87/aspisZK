import PV_B3P_P227_10
import PV_B3P_ReadFunctions9227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error
set_option autoImplicit false

/-- Exact emitted body context; only the immutable-read callee is abstracted. -/
def reference_terminal_add_value_lanes_read_context9 (source_read : ({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)) (packed : Array aspis_core.field.QM31 24#usize)
  (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : reference_copy_terminal.Selectors)  :
  Result (Array aspis_core.field.QM31 24#usize) :=  do
  let i ←
    lift (Std.Usize.wrapping_mul 16#usize
      reference_terminal.VALUE_AUXILIARY_BLOCK)
  let q ← reference_copy_terminal.Selectors.row selectors i
  let i1 ←
    lift (Std.Usize.wrapping_mul 16#usize
      reference_terminal.VALUE_AUXILIARY_BLOCK)
  let i2 ← lift (Std.Usize.wrapping_add i1 2#usize)
  let q1 ← reference_copy_terminal.Selectors.row selectors i2
  let i3 ←
    lift (Std.Usize.wrapping_mul 16#usize
      reference_terminal.VALUE_AUXILIARY_BLOCK)
  let i4 ← lift (Std.Usize.wrapping_add i3 4#usize)
  let q2 ← reference_copy_terminal.Selectors.row selectors i4
  let q3 ← Array.index_usize (Array.make 3#usize [ q, q1, q2 ] (by simp only [List.length_cons,List.length_nil]; rfl)) 0#usize
  let q4 ← aspis_core.field.QM31.add aspis_core.field.QM31.ZERO q3
  let q5 ← Array.index_usize (Array.make 3#usize [ q, q1, q2 ] (by simp only [List.length_cons,List.length_nil]; rfl)) 1#usize
  let q6 ← aspis_core.field.QM31.add q4 q5
  let q7 ← Array.index_usize (Array.make 3#usize [ q, q1, q2 ] (by simp only [List.length_cons,List.length_nil]; rfl)) 2#usize
  let range_selector ← aspis_core.field.QM31.add q6 q7
  let range := Array.repeat 33#usize aspis_core.field.QM31.ZERO
  let q8 ← source_read openings.z 0#usize
  let q9 ← aspis_core.field.QM31.square q8
  let q10 ← aspis_core.field.QM31.sub q9 q8
  let range1 ← Array.update range 0#usize q10
  let q11 ← source_read openings.z 1#usize
  let q12 ← aspis_core.field.QM31.square q11
  let q13 ← aspis_core.field.QM31.sub q12 q11
  let range2 ← Array.update range1 1#usize q13
  let q14 ← source_read openings.z 2#usize
  let q15 ← aspis_core.field.QM31.square q14
  let q16 ← aspis_core.field.QM31.sub q15 q14
  let range3 ← Array.update range2 2#usize q16
  let q17 ← source_read openings.z 3#usize
  let q18 ← aspis_core.field.QM31.square q17
  let q19 ← aspis_core.field.QM31.sub q18 q17
  let range4 ← Array.update range3 3#usize q19
  let q20 ← source_read openings.z 4#usize
  let q21 ← aspis_core.field.QM31.square q20
  let q22 ← aspis_core.field.QM31.sub q21 q20
  let range5 ← Array.update range4 4#usize q22
  let q23 ← source_read openings.z 5#usize
  let q24 ← aspis_core.field.QM31.square q23
  let q25 ← aspis_core.field.QM31.sub q24 q23
  let range6 ← Array.update range5 5#usize q25
  let q26 ← source_read openings.z 6#usize
  let q27 ← aspis_core.field.QM31.square q26
  let q28 ← aspis_core.field.QM31.sub q27 q26
  let range7 ← Array.update range6 6#usize q28
  let q29 ← source_read openings.z 7#usize
  let q30 ← aspis_core.field.QM31.square q29
  let q31 ← aspis_core.field.QM31.sub q30 q29
  let range8 ← Array.update range7 7#usize q31
  let q32 ← source_read openings.z 8#usize
  let q33 ← aspis_core.field.QM31.square q32
  let q34 ← aspis_core.field.QM31.sub q33 q32
  let range9 ← Array.update range8 8#usize q34
  let q35 ← source_read openings.z 9#usize
  let q36 ← aspis_core.field.QM31.square q35
  let q37 ← aspis_core.field.QM31.sub q36 q35
  let range10 ← Array.update range9 9#usize q37
  let q38 ← source_read openings.succ_z 0#usize
  let q39 ← aspis_core.field.QM31.square q38
  let q40 ← aspis_core.field.QM31.sub q39 q38
  let i5 ← lift (Std.Usize.wrapping_add 10#usize 0#usize)
  let range11 ← Array.update range10 i5 q40
  let q41 ← source_read openings.succ_z 1#usize
  let q42 ← aspis_core.field.QM31.square q41
  let q43 ← aspis_core.field.QM31.sub q42 q41
  let i6 ← lift (Std.Usize.wrapping_add 10#usize 1#usize)
  let range12 ← Array.update range11 i6 q43
  let q44 ← source_read openings.succ_z 2#usize
  let q45 ← aspis_core.field.QM31.square q44
  let q46 ← aspis_core.field.QM31.sub q45 q44
  let i7 ← lift (Std.Usize.wrapping_add 10#usize 2#usize)
  let range13 ← Array.update range12 i7 q46
  let q47 ← source_read openings.succ_z 3#usize
  let q48 ← aspis_core.field.QM31.square q47
  let q49 ← aspis_core.field.QM31.sub q48 q47
  let i8 ← lift (Std.Usize.wrapping_add 10#usize 3#usize)
  let range14 ← Array.update range13 i8 q49
  let q50 ← source_read openings.succ_z 4#usize
  let q51 ← aspis_core.field.QM31.square q50
  let q52 ← aspis_core.field.QM31.sub q51 q50
  let i9 ← lift (Std.Usize.wrapping_add 10#usize 4#usize)
  let range15 ← Array.update range14 i9 q52
  let q53 ← source_read openings.succ_z 5#usize
  let q54 ← aspis_core.field.QM31.square q53
  let q55 ← aspis_core.field.QM31.sub q54 q53
  let i10 ← lift (Std.Usize.wrapping_add 10#usize 5#usize)
  let range16 ← Array.update range15 i10 q55
  let q56 ← source_read openings.succ_z 6#usize
  let q57 ← aspis_core.field.QM31.square q56
  let q58 ← aspis_core.field.QM31.sub q57 q56
  let i11 ← lift (Std.Usize.wrapping_add 10#usize 6#usize)
  let range17 ← Array.update range16 i11 q58
  let q59 ← source_read openings.succ_z 7#usize
  let q60 ← aspis_core.field.QM31.square q59
  let q61 ← aspis_core.field.QM31.sub q60 q59
  let i12 ← lift (Std.Usize.wrapping_add 10#usize 7#usize)
  let range18 ← Array.update range17 i12 q61
  let q62 ← source_read openings.succ_z 8#usize
  let q63 ← aspis_core.field.QM31.square q62
  let q64 ← aspis_core.field.QM31.sub q63 q62
  let i13 ← lift (Std.Usize.wrapping_add 10#usize 8#usize)
  let range19 ← Array.update range18 i13 q64
  let q65 ← source_read openings.succ_z 9#usize
  let q66 ← aspis_core.field.QM31.square q65
  let q67 ← aspis_core.field.QM31.sub q66 q65
  let i14 ← lift (Std.Usize.wrapping_add 10#usize 9#usize)
  let range20 ← Array.update range19 i14 q67
  let q68 ← source_read openings.xor12_z 0#usize
  let q69 ← aspis_core.field.QM31.square q68
  let q70 ← aspis_core.field.QM31.sub q69 q68
  let i15 ← lift (Std.Usize.wrapping_add 20#usize 0#usize)
  let range21 ← Array.update range20 i15 q70
  let q71 ← source_read openings.xor12_z 1#usize
  let q72 ← aspis_core.field.QM31.square q71
  let q73 ← aspis_core.field.QM31.sub q72 q71
  let i16 ← lift (Std.Usize.wrapping_add 20#usize 1#usize)
  let range22 ← Array.update range21 i16 q73
  let q74 ← source_read openings.xor12_z 2#usize
  let q75 ← aspis_core.field.QM31.square q74
  let q76 ← aspis_core.field.QM31.sub q75 q74
  let i17 ← lift (Std.Usize.wrapping_add 20#usize 2#usize)
  let range23 ← Array.update range22 i17 q76
  let q77 ← source_read openings.xor12_z 3#usize
  let q78 ← aspis_core.field.QM31.square q77
  let q79 ← aspis_core.field.QM31.sub q78 q77
  let i18 ← lift (Std.Usize.wrapping_add 20#usize 3#usize)
  let range24 ← Array.update range23 i18 q79
  let q80 ← source_read openings.xor12_z 4#usize
  let q81 ← aspis_core.field.QM31.square q80
  let q82 ← aspis_core.field.QM31.sub q81 q80
  let i19 ← lift (Std.Usize.wrapping_add 20#usize 4#usize)
  let range25 ← Array.update range24 i19 q82
  let q83 ← source_read openings.xor12_z 5#usize
  let q84 ← aspis_core.field.QM31.square q83
  let q85 ← aspis_core.field.QM31.sub q84 q83
  let i20 ← lift (Std.Usize.wrapping_add 20#usize 5#usize)
  let range26 ← Array.update range25 i20 q85
  let q86 ← source_read openings.xor12_z 6#usize
  let q87 ← aspis_core.field.QM31.square q86
  let q88 ← aspis_core.field.QM31.sub q87 q86
  let i21 ← lift (Std.Usize.wrapping_add 20#usize 6#usize)
  let range27 ← Array.update range26 i21 q88
  let q89 ← source_read openings.xor12_z 7#usize
  let q90 ← aspis_core.field.QM31.square q89
  let q91 ← aspis_core.field.QM31.sub q90 q89
  let i22 ← lift (Std.Usize.wrapping_add 20#usize 7#usize)
  let range28 ← Array.update range27 i22 q91
  let q92 ← source_read openings.xor12_z 8#usize
  let q93 ← aspis_core.field.QM31.square q92
  let q94 ← aspis_core.field.QM31.sub q93 q92
  let i23 ← lift (Std.Usize.wrapping_add 20#usize 8#usize)
  let range29 ← Array.update range28 i23 q94
  let q95 ← source_read openings.xor12_z 9#usize
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
  let q108 ← source_read range33 0#usize
  let q109 ← aspis_core.field.QM31.mul range_selector q108
  let range34 ← Array.update range33 0#usize q109
  let q110 ← source_read range34 1#usize
  let q111 ← aspis_core.field.QM31.mul range_selector q110
  let range35 ← Array.update range34 1#usize q111
  let q112 ← source_read range35 2#usize
  let q113 ← aspis_core.field.QM31.mul range_selector q112
  let range36 ← Array.update range35 2#usize q113
  let q114 ← source_read range36 3#usize
  let q115 ← aspis_core.field.QM31.mul range_selector q114
  let range37 ← Array.update range36 3#usize q115
  let q116 ← source_read range37 4#usize
  let q117 ← aspis_core.field.QM31.mul range_selector q116
  let range38 ← Array.update range37 4#usize q117
  let q118 ← source_read range38 5#usize
  let q119 ← aspis_core.field.QM31.mul range_selector q118
  let range39 ← Array.update range38 5#usize q119
  let q120 ← source_read range39 6#usize
  let q121 ← aspis_core.field.QM31.mul range_selector q120
  let range40 ← Array.update range39 6#usize q121
  let q122 ← source_read range40 7#usize
  let q123 ← aspis_core.field.QM31.mul range_selector q122
  let range41 ← Array.update range40 7#usize q123
  let q124 ← source_read range41 8#usize
  let q125 ← aspis_core.field.QM31.mul range_selector q124
  let range42 ← Array.update range41 8#usize q125
  let q126 ← source_read range42 9#usize
  let q127 ← aspis_core.field.QM31.mul range_selector q126
  let range43 ← Array.update range42 9#usize q127
  let q128 ← source_read range43 10#usize
  let q129 ← aspis_core.field.QM31.mul range_selector q128
  let range44 ← Array.update range43 10#usize q129
  let q130 ← source_read range44 11#usize
  let q131 ← aspis_core.field.QM31.mul range_selector q130
  let range45 ← Array.update range44 11#usize q131
  let q132 ← source_read range45 12#usize
  let q133 ← aspis_core.field.QM31.mul range_selector q132
  let range46 ← Array.update range45 12#usize q133
  let q134 ← source_read range46 13#usize
  let q135 ← aspis_core.field.QM31.mul range_selector q134
  let range47 ← Array.update range46 13#usize q135
  let q136 ← source_read range47 14#usize
  let q137 ← aspis_core.field.QM31.mul range_selector q136
  let range48 ← Array.update range47 14#usize q137
  let q138 ← source_read range48 15#usize
  let q139 ← aspis_core.field.QM31.mul range_selector q138
  let range49 ← Array.update range48 15#usize q139
  let q140 ← source_read range49 16#usize
  let q141 ← aspis_core.field.QM31.mul range_selector q140
  let range50 ← Array.update range49 16#usize q141
  let q142 ← source_read range50 17#usize
  let q143 ← aspis_core.field.QM31.mul range_selector q142
  let range51 ← Array.update range50 17#usize q143
  let q144 ← source_read range51 18#usize
  let q145 ← aspis_core.field.QM31.mul range_selector q144
  let range52 ← Array.update range51 18#usize q145
  let q146 ← source_read range52 19#usize
  let q147 ← aspis_core.field.QM31.mul range_selector q146
  let range53 ← Array.update range52 19#usize q147
  let q148 ← source_read range53 20#usize
  let q149 ← aspis_core.field.QM31.mul range_selector q148
  let range54 ← Array.update range53 20#usize q149
  let q150 ← source_read range54 21#usize
  let q151 ← aspis_core.field.QM31.mul range_selector q150
  let range55 ← Array.update range54 21#usize q151
  let q152 ← source_read range55 22#usize
  let q153 ← aspis_core.field.QM31.mul range_selector q152
  let range56 ← Array.update range55 22#usize q153
  let q154 ← source_read range56 23#usize
  let q155 ← aspis_core.field.QM31.mul range_selector q154
  let range57 ← Array.update range56 23#usize q155
  let q156 ← source_read range57 24#usize
  let q157 ← aspis_core.field.QM31.mul range_selector q156
  let range58 ← Array.update range57 24#usize q157
  let q158 ← source_read range58 25#usize
  let q159 ← aspis_core.field.QM31.mul range_selector q158
  let range59 ← Array.update range58 25#usize q159
  let q160 ← source_read range59 26#usize
  let q161 ← aspis_core.field.QM31.mul range_selector q160
  let range60 ← Array.update range59 26#usize q161
  let q162 ← source_read range60 27#usize
  let q163 ← aspis_core.field.QM31.mul range_selector q162
  let range61 ← Array.update range60 27#usize q163
  let q164 ← source_read range61 28#usize
  let q165 ← aspis_core.field.QM31.mul range_selector q164
  let range62 ← Array.update range61 28#usize q165
  let q166 ← source_read range62 29#usize
  let q167 ← aspis_core.field.QM31.mul range_selector q166
  let range63 ← Array.update range62 29#usize q167
  let q168 ← source_read range63 30#usize
  let q169 ← aspis_core.field.QM31.mul range_selector q168
  let range64 ← Array.update range63 30#usize q169
  let q170 ← source_read range64 31#usize
  let q171 ← aspis_core.field.QM31.mul range_selector q170
  let range65 ← Array.update range64 31#usize q171
  let q172 ← source_read range65 32#usize
  let q173 ← aspis_core.field.QM31.mul range_selector q172
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

def reference_terminal_add_value_lanes_direct_read9 (packed : Array aspis_core.field.QM31 24#usize)
  (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : reference_copy_terminal.Selectors)  :
  Result (Array aspis_core.field.QM31 24#usize) :=
  reference_terminal_add_value_lanes_read_context9 (fun values i => Array.index_usize values i) packed openings selectors

theorem reference_terminal_add_value_lanes_read_binding9 (packed : Array aspis_core.field.QM31 24#usize)
  (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : reference_copy_terminal.Selectors)  :
    reference_terminal.add_value_lanes packed openings selectors = reference_terminal_add_value_lanes_direct_read9 packed openings selectors :=
  congrArg (fun source_read => reference_terminal_add_value_lanes_read_context9 source_read packed openings selectors) read_function_binding

#print axioms reference_terminal_add_value_lanes_read_binding9
end PV_B3P_Binding9227
