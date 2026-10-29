import PV_B3P_ProjectedStage132227
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
def projected_stage13_1 (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (leading full : Array aspis_core.field.QM31 4#usize) (internal : Array aspis_core.field.QM31 16#usize) (pqm pqm1 pqm2 prepared_block : reference_field.PreparedQm31Multiplier) (q32 : aspis_core.field.QM31) : Result (Array aspis_core.field.QM31 4#usize) := do
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
  projected_stage13_2 openings leading full internal pqm pqm1 pqm2 prepared_block q32 q47
end PV_B3P_Binding13227
