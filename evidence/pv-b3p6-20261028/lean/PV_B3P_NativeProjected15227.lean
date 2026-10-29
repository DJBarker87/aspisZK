import PV_B3P_NativeLeading15227
import PV_B3P_ProjectedLink13227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227 PV_B3P_Success227 Result
set_option autoImplicit false

def native_projected15 := projected_prefix13 native_leading15

theorem native_projected_binding15
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : aspis_statement.state_only_poseidon.StateOnlyPoseidonSelectors) :
    native_projected15 openings selectors = reference_poseidon.evaluate_state_only_poseidon_oracle_projected openings selectors := by
  have leading : native_leading15 = reference_poseidon.leading_pair_packed := funext native_leading_binding15
  unfold native_projected15
  rw [leading]
  exact (projected_staging13 openings selectors).symm
#print axioms native_projected_binding15
end PV_B3P_Native15227
