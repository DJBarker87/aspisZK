import PV_B3P_ProjectedPrefix13227
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
theorem projected_staging13
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : aspis_statement.state_only_poseidon.StateOnlyPoseidonSelectors) :
    reference_poseidon.evaluate_state_only_poseidon_oracle_projected openings selectors =
      projected_prefix13 reference_poseidon.leading_pair_packed openings selectors := by
  unfold reference_poseidon.evaluate_state_only_poseidon_oracle_projected projected_prefix13
    projected_stage13_0 projected_stage13_1 projected_stage13_2 projected_stage13_3
  rfl

theorem projected_actual_leading13
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : aspis_statement.state_only_poseidon.StateOnlyPoseidonSelectors) :
    reference_poseidon.evaluate_state_only_poseidon_oracle_projected openings selectors =
      projected_prefix13 source_leading12 openings selectors :=
  Eq.trans (projected_staging13 openings selectors) (projected_prefix_leading13 openings selectors)
#print axioms projected_staging13
#print axioms projected_actual_leading13
end PV_B3P_Binding13227
