import PV_B3P_P227_14
import PV_B3P_InternalBinding12227
import PV_B3P_ValueCallerBridge12227
import PV_B3P_PatternBinding12227
import PV_B3P_Operations12227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error
set_option autoImplicit false
def actual_context12_4 (operation : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings → Result (Array aspis_core.field.QM31 4#usize))
  (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : aspis_statement.state_only_poseidon.StateOnlyPoseidonSelectors)
  :
  Result (Array aspis_core.field.QM31 4#usize)
  := do
  let leading_low ← Array.index_usize selectors.«local» 0#usize
  let q ← Array.index_usize selectors.«local» 1#usize
  let q1 ← aspis_core.field.QM31.add aspis_core.field.QM31.ZERO q
  let q2 ← Array.index_usize selectors.«local» 9#usize
  let q3 ← aspis_core.field.QM31.add q1 q2
  let q4 ← Array.index_usize selectors.«local» 10#usize
  let full_low ← aspis_core.field.QM31.add q3 q4
  let q5 ← Array.index_usize selectors.«local» 2#usize
  let q6 ← aspis_core.field.QM31.add aspis_core.field.QM31.ZERO q5
  let q7 ← Array.index_usize selectors.«local» 3#usize
  let q8 ← aspis_core.field.QM31.add q6 q7
  let q9 ← Array.index_usize selectors.«local» 4#usize
  let q10 ← aspis_core.field.QM31.add q8 q9
  let q11 ← Array.index_usize selectors.«local» 5#usize
  let q12 ← aspis_core.field.QM31.add q10 q11
  let q13 ← Array.index_usize selectors.«local» 6#usize
  let q14 ← aspis_core.field.QM31.add q12 q13
  let q15 ← Array.index_usize selectors.«local» 7#usize
  let q16 ← aspis_core.field.QM31.add q14 q15
  let q17 ← Array.index_usize selectors.«local» 8#usize
  let internal_low ← aspis_core.field.QM31.add q16 q17
  let leading ← operation openings
  let full ←
    reference_poseidon.interpolated_full_pair_packed openings.z
      selectors.«local»
  let internal ←
    reference_poseidon.interpolated_internal_pair openings.z
      selectors.«local»
  let pqm ← reference_field.PreparedQm31Multiplier.new leading_low
  let pqm1 ← reference_field.PreparedQm31Multiplier.new full_low
  let pqm2 ← reference_field.PreparedQm31Multiplier.new internal_low
  let prepared_block ←
    reference_field.PreparedQm31Multiplier.new selectors.block
  let start ← lift (Std.Usize.wrapping_mul 4#usize 0#usize)
  let i ← lift (Std.Usize.wrapping_add start 0#usize)
  let q18 ← Array.index_usize openings.succ_z i
  let i1 ← lift (Std.Usize.wrapping_add start 1#usize)
  let q19 ← Array.index_usize openings.succ_z i1
  let i2 ← lift (Std.Usize.wrapping_add start 2#usize)
  let q20 ← Array.index_usize openings.succ_z i2
  let i3 ← lift (Std.Usize.wrapping_add start 3#usize)
  let q21 ← Array.index_usize openings.succ_z i3
  let s ← lift (Array.to_slice (Array.make 4#usize [ q18, q19, q20, q21 ]))
  let target ← reference_field.qm31_pack_base4 s
  let i4 ← lift (Std.Usize.wrapping_add start 0#usize)
  let q22 ← Array.index_usize internal i4
  let i5 ← lift (Std.Usize.wrapping_add start 1#usize)
  let q23 ← Array.index_usize internal i5
  let i6 ← lift (Std.Usize.wrapping_add start 2#usize)
  let q24 ← Array.index_usize internal i6
  let i7 ← lift (Std.Usize.wrapping_add start 3#usize)
  let q25 ← Array.index_usize internal i7
  let s1 ← lift (Array.to_slice (Array.make 4#usize [ q22, q23, q24, q25 ]))
  let internal1 ← reference_field.qm31_pack_base4 s1
  let q26 ← Array.index_usize leading 0#usize
  let q27 ← aspis_core.field.QM31.sub target q26
  let q28 ← Array.index_usize full 0#usize
  let q29 ← aspis_core.field.QM31.sub target q28
  let q30 ← aspis_core.field.QM31.sub target internal1
  let q31 ←
    reference_field.qm31_sum_products3_prepared
      (Array.make 3#usize [ pqm, pqm1, pqm2 ])
      (Array.make 3#usize [ q27, q29, q30 ])
  let q32 ← reference_field.PreparedQm31Multiplier.mul prepared_block q31
  let start1 ← lift (Std.Usize.wrapping_mul 4#usize 1#usize)
  let i8 ← lift (Std.Usize.wrapping_add start1 0#usize)
  let q33 ← Array.index_usize openings.succ_z i8
  let i9 ← lift (Std.Usize.wrapping_add start1 1#usize)
  let q34 ← Array.index_usize openings.succ_z i9
  let i10 ← lift (Std.Usize.wrapping_add start1 2#usize)
  let q35 ← Array.index_usize openings.succ_z i10
  let i11 ← lift (Std.Usize.wrapping_add start1 3#usize)
  let q36 ← Array.index_usize openings.succ_z i11
  let s2 ← lift (Array.to_slice (Array.make 4#usize [ q33, q34, q35, q36 ]))
  let target1 ← reference_field.qm31_pack_base4 s2
  let i12 ← lift (Std.Usize.wrapping_add start1 0#usize)
  let q37 ← Array.index_usize internal i12
  let i13 ← lift (Std.Usize.wrapping_add start1 1#usize)
  let q38 ← Array.index_usize internal i13
  let i14 ← lift (Std.Usize.wrapping_add start1 2#usize)
  let q39 ← Array.index_usize internal i14
  let i15 ← lift (Std.Usize.wrapping_add start1 3#usize)
  let q40 ← Array.index_usize internal i15
  let s3 ← lift (Array.to_slice (Array.make 4#usize [ q37, q38, q39, q40 ]))
  let internal2 ← reference_field.qm31_pack_base4 s3
  let q41 ← Array.index_usize leading 1#usize
  let q42 ← aspis_core.field.QM31.sub target1 q41
  let q43 ← Array.index_usize full 1#usize
  let q44 ← aspis_core.field.QM31.sub target1 q43
  let q45 ← aspis_core.field.QM31.sub target1 internal2
  let q46 ←
    reference_field.qm31_sum_products3_prepared
      (Array.make 3#usize [ pqm, pqm1, pqm2 ])
      (Array.make 3#usize [ q42, q44, q45 ])
  let q47 ← reference_field.PreparedQm31Multiplier.mul prepared_block q46
  let start2 ← lift (Std.Usize.wrapping_mul 4#usize 2#usize)
  let i16 ← lift (Std.Usize.wrapping_add start2 0#usize)
  let q48 ← Array.index_usize openings.succ_z i16
  let i17 ← lift (Std.Usize.wrapping_add start2 1#usize)
  let q49 ← Array.index_usize openings.succ_z i17
  let i18 ← lift (Std.Usize.wrapping_add start2 2#usize)
  let q50 ← Array.index_usize openings.succ_z i18
  let i19 ← lift (Std.Usize.wrapping_add start2 3#usize)
  let q51 ← Array.index_usize openings.succ_z i19
  let s4 ← lift (Array.to_slice (Array.make 4#usize [ q48, q49, q50, q51 ]))
  let target2 ← reference_field.qm31_pack_base4 s4
  let i20 ← lift (Std.Usize.wrapping_add start2 0#usize)
  let q52 ← Array.index_usize internal i20
  let i21 ← lift (Std.Usize.wrapping_add start2 1#usize)
  let q53 ← Array.index_usize internal i21
  let i22 ← lift (Std.Usize.wrapping_add start2 2#usize)
  let q54 ← Array.index_usize internal i22
  let i23 ← lift (Std.Usize.wrapping_add start2 3#usize)
  let q55 ← Array.index_usize internal i23
  let s5 ← lift (Array.to_slice (Array.make 4#usize [ q52, q53, q54, q55 ]))
  let internal3 ← reference_field.qm31_pack_base4 s5
  let q56 ← Array.index_usize leading 2#usize
  let q57 ← aspis_core.field.QM31.sub target2 q56
  let q58 ← Array.index_usize full 2#usize
  let q59 ← aspis_core.field.QM31.sub target2 q58
  let q60 ← aspis_core.field.QM31.sub target2 internal3
  let q61 ←
    reference_field.qm31_sum_products3_prepared
      (Array.make 3#usize [ pqm, pqm1, pqm2 ])
      (Array.make 3#usize [ q57, q59, q60 ])
  let q62 ← reference_field.PreparedQm31Multiplier.mul prepared_block q61
  let start3 ← lift (Std.Usize.wrapping_mul 4#usize 3#usize)
  let i24 ← lift (Std.Usize.wrapping_add start3 0#usize)
  let q63 ← Array.index_usize openings.succ_z i24
  let i25 ← lift (Std.Usize.wrapping_add start3 1#usize)
  let q64 ← Array.index_usize openings.succ_z i25
  let i26 ← lift (Std.Usize.wrapping_add start3 2#usize)
  let q65 ← Array.index_usize openings.succ_z i26
  let i27 ← lift (Std.Usize.wrapping_add start3 3#usize)
  let q66 ← Array.index_usize openings.succ_z i27
  let s6 ← lift (Array.to_slice (Array.make 4#usize [ q63, q64, q65, q66 ]))
  let target3 ← reference_field.qm31_pack_base4 s6
  let i28 ← lift (Std.Usize.wrapping_add start3 0#usize)
  let q67 ← Array.index_usize internal i28
  let i29 ← lift (Std.Usize.wrapping_add start3 1#usize)
  let q68 ← Array.index_usize internal i29
  let i30 ← lift (Std.Usize.wrapping_add start3 2#usize)
  let q69 ← Array.index_usize internal i30
  let i31 ← lift (Std.Usize.wrapping_add start3 3#usize)
  let q70 ← Array.index_usize internal i31
  let s7 ← lift (Array.to_slice (Array.make 4#usize [ q67, q68, q69, q70 ]))
  let internal4 ← reference_field.qm31_pack_base4 s7
  let q71 ← Array.index_usize leading 3#usize
  let q72 ← aspis_core.field.QM31.sub target3 q71
  let q73 ← Array.index_usize full 3#usize
  let q74 ← aspis_core.field.QM31.sub target3 q73
  let q75 ← aspis_core.field.QM31.sub target3 internal4
  let q76 ←
    reference_field.qm31_sum_products3_prepared
      (Array.make 3#usize [ pqm, pqm1, pqm2 ])
      (Array.make 3#usize [ q72, q74, q75 ])
  let q77 ← reference_field.PreparedQm31Multiplier.mul prepared_block q76
  ok (Array.make 4#usize [ q32, q47, q62, q77 ])
theorem actual_caller_binding12_4 
  (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : aspis_statement.state_only_poseidon.StateOnlyPoseidonSelectors)
  :
    @reference_poseidon.evaluate_state_only_poseidon_oracle_projected openings selectors = @actual_context12_4 source_leading12 openings selectors :=
  congrArg (fun (operation : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings → Result (Array aspis_core.field.QM31 4#usize)) => @actual_context12_4 operation openings selectors) leading_operation12
#print axioms actual_caller_binding12_4
end PV_B3P_Binding12227
