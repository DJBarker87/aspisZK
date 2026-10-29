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
def projected_stage13_3 (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (leading full : Array aspis_core.field.QM31 4#usize) (internal : Array aspis_core.field.QM31 16#usize) (pqm pqm1 pqm2 prepared_block : reference_field.PreparedQm31Multiplier) (q32 q47 q62 : aspis_core.field.QM31) : Result (Array aspis_core.field.QM31 4#usize) := do
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
end PV_B3P_Binding13227
