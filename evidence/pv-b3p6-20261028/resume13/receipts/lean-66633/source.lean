import PV_B3P_ProjectedStage133227
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
def projected_stage13_2 (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (leading full : Array aspis_core.field.QM31 4#usize) (internal : Array aspis_core.field.QM31 16#usize) (pqm pqm1 pqm2 prepared_block : reference_field.PreparedQm31Multiplier) (q32 q47 : aspis_core.field.QM31) : Result (Array aspis_core.field.QM31 4#usize) := do
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
  projected_stage13_3 openings leading full internal pqm pqm1 pqm2 prepared_block q32 q47 q62
end PV_B3P_Binding13227
