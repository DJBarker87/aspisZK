import PV_B3P_LeadingSource546227
import PV_B3P_ProjectedLink13227
namespace PV_B3P_Association547227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding13227 PV_B3P_Association546227
set_option autoImplicit false

/-- The concrete staged projected caller, using the bound source leading body. -/
def source_projected547 := projected_prefix13 source_leading546

theorem projected_source_reference547
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : aspis_statement.state_only_poseidon.StateOnlyPoseidonSelectors) :
    source_projected547 openings selectors =
      reference_poseidon.evaluate_state_only_poseidon_oracle_projected openings selectors := by
  have leading : source_leading546 = reference_poseidon.leading_pair_packed :=
    funext leading_source_reference546
  unfold source_projected547
  rw [leading]
  exact (projected_staging13 openings selectors).symm

theorem projected_source_link547 :
    PV_B3P_Links13227.PV_B3P_Link_poseidon_evaluate_state_only_poseidon_oracle_projected source_projected547 :=
  funext fun openings => funext fun selectors => projected_source_reference547 openings selectors

#print axioms projected_source_reference547
#print axioms projected_source_link547
end PV_B3P_Association547227
