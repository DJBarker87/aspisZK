import PV_B3P_ProjectedStores13227
import PV_B3P_LinkDefinitions13227
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
def source_projected13 (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (selectors : aspis_statement.state_only_poseidon.StateOnlyPoseidonSelectors) : Result (Array aspis_core.field.QM31 4#usize) := do

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
  let leading ← source_leading12 openings
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
  projected_output_loop13 openings leading full internal pqm pqm1 pqm2 prepared_block
theorem source_projected_prefix13
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : aspis_statement.state_only_poseidon.StateOnlyPoseidonSelectors) :
    source_projected13 openings selectors = projected_prefix13 source_leading12 openings selectors := by
  unfold source_projected13 projected_prefix13
  apply congrArg (Aeneas.Std.bind _)
  funext leading_low
  apply congrArg (Aeneas.Std.bind _)
  funext q
  apply congrArg (Aeneas.Std.bind _)
  funext q1
  apply congrArg (Aeneas.Std.bind _)
  funext q2
  apply congrArg (Aeneas.Std.bind _)
  funext q3
  apply congrArg (Aeneas.Std.bind _)
  funext q4
  apply congrArg (Aeneas.Std.bind _)
  funext full_low
  apply congrArg (Aeneas.Std.bind _)
  funext q5
  apply congrArg (Aeneas.Std.bind _)
  funext q6
  apply congrArg (Aeneas.Std.bind _)
  funext q7
  apply congrArg (Aeneas.Std.bind _)
  funext q8
  apply congrArg (Aeneas.Std.bind _)
  funext q9
  apply congrArg (Aeneas.Std.bind _)
  funext q10
  apply congrArg (Aeneas.Std.bind _)
  funext q11
  apply congrArg (Aeneas.Std.bind _)
  funext q12
  apply congrArg (Aeneas.Std.bind _)
  funext q13
  apply congrArg (Aeneas.Std.bind _)
  funext q14
  apply congrArg (Aeneas.Std.bind _)
  funext q15
  apply congrArg (Aeneas.Std.bind _)
  funext q16
  apply congrArg (Aeneas.Std.bind _)
  funext q17
  apply congrArg (Aeneas.Std.bind _)
  funext internal_low
  apply congrArg (Aeneas.Std.bind _)
  funext leading
  apply congrArg (Aeneas.Std.bind _)
  funext full
  apply congrArg (Aeneas.Std.bind _)
  funext internal
  apply congrArg (Aeneas.Std.bind _)
  funext pqm
  apply congrArg (Aeneas.Std.bind _)
  funext pqm1
  apply congrArg (Aeneas.Std.bind _)
  funext pqm2
  apply congrArg (Aeneas.Std.bind _)
  funext prepared_block
  exact projected_output_loop_binding13 openings leading full internal pqm pqm1 pqm2 prepared_block
theorem projected_link13 :
    PV_B3P_Links13227.PV_B3P_Link_poseidon_evaluate_state_only_poseidon_oracle_projected source_projected13 := by
  funext openings selectors
  exact Eq.trans (source_projected_prefix13 openings selectors) (projected_actual_leading13 openings selectors).symm
#print axioms source_projected_prefix13
#print axioms projected_link13
end PV_B3P_Binding13227
