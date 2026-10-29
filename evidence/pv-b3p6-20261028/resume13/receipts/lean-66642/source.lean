import PV_B3P_ProjectedStage130227
import PV_B3P_ProjectedRaw131227
import PV_B3P_P227_14
import PV_B3P_Operations12227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding12227 Result
set_option autoImplicit false
attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.sub
  aspis_core.field.QM31.mul reference_field.qm31_pack_base4
  reference_field.qm31_sum_products3_prepared reference_field.PreparedQm31Multiplier.mul
  reference_field.PreparedQm31Multiplier.new reference_poseidon.interpolated_full_pair_packed
  reference_poseidon.interpolated_internal_pair reference_poseidon.leading_pair_packed
def projected_raw13_0 (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (leading full : Array aspis_core.field.QM31 4#usize) (internal : Array aspis_core.field.QM31 16#usize) (pqm pqm1 pqm2 prepared_block : reference_field.PreparedQm31Multiplier) : Result (Array aspis_core.field.QM31 4#usize) := do
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
theorem projected_raw_binding13_0 (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (leading full : Array aspis_core.field.QM31 4#usize) (internal : Array aspis_core.field.QM31 16#usize) (pqm pqm1 pqm2 prepared_block : reference_field.PreparedQm31Multiplier) : projected_raw13_0 openings leading full internal pqm pqm1 pqm2 prepared_block  = projected_stage13_0 openings leading full internal pqm pqm1 pqm2 prepared_block  := by
  unfold projected_raw13_0 projected_stage13_0
  apply congrArg (Aeneas.Std.bind _)
  funext start
  apply congrArg (Aeneas.Std.bind _)
  funext i
  apply congrArg (Aeneas.Std.bind _)
  funext q18
  apply congrArg (Aeneas.Std.bind _)
  funext i1
  apply congrArg (Aeneas.Std.bind _)
  funext q19
  apply congrArg (Aeneas.Std.bind _)
  funext i2
  apply congrArg (Aeneas.Std.bind _)
  funext q20
  apply congrArg (Aeneas.Std.bind _)
  funext i3
  apply congrArg (Aeneas.Std.bind _)
  funext q21
  apply congrArg (Aeneas.Std.bind _)
  funext s
  apply congrArg (Aeneas.Std.bind _)
  funext target
  apply congrArg (Aeneas.Std.bind _)
  funext i4
  apply congrArg (Aeneas.Std.bind _)
  funext q22
  apply congrArg (Aeneas.Std.bind _)
  funext i5
  apply congrArg (Aeneas.Std.bind _)
  funext q23
  apply congrArg (Aeneas.Std.bind _)
  funext i6
  apply congrArg (Aeneas.Std.bind _)
  funext q24
  apply congrArg (Aeneas.Std.bind _)
  funext i7
  apply congrArg (Aeneas.Std.bind _)
  funext q25
  apply congrArg (Aeneas.Std.bind _)
  funext s1
  apply congrArg (Aeneas.Std.bind _)
  funext internal1
  apply congrArg (Aeneas.Std.bind _)
  funext q26
  apply congrArg (Aeneas.Std.bind _)
  funext q27
  apply congrArg (Aeneas.Std.bind _)
  funext q28
  apply congrArg (Aeneas.Std.bind _)
  funext q29
  apply congrArg (Aeneas.Std.bind _)
  funext q30
  apply congrArg (Aeneas.Std.bind _)
  funext q31
  apply congrArg (Aeneas.Std.bind _)
  funext q32
  exact projected_raw_binding13_1 openings leading full internal pqm pqm1 pqm2 prepared_block q32
#print axioms projected_raw_binding13_0
end PV_B3P_Binding13227
