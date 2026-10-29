import PV_B3P_ProjectedStage131227
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
def projected_stage13_0 (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (leading full : Array aspis_core.field.QM31 4#usize) (internal : Array aspis_core.field.QM31 16#usize) (pqm pqm1 pqm2 prepared_block : reference_field.PreparedQm31Multiplier) : Result (Array aspis_core.field.QM31 4#usize) := do
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
  projected_stage13_1 openings leading full internal pqm pqm1 pqm2 prepared_block q32
end PV_B3P_Binding13227
