import PV_B3P_LinkDefinitions13227
import PV_B3P_Operations12227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Links13227 PV_B3P_Binding9227 PV_B3P_Binding10227 PV_B3P_Binding11227 PV_B3P_Binding12227
set_option autoImplicit false
def source_round13_QPlain  (state : RoundState10) (constants1 : Array aspis_core.field.QM31 16#usize) := (PV_B3P_Ordered227.fold (round_q_step10 constants1) [0#usize, 1#usize, 2#usize, 3#usize, 4#usize, 5#usize, 6#usize, 7#usize, 8#usize, 9#usize, 10#usize, 11#usize, 12#usize, 13#usize, 14#usize, 15#usize] state >>= reference_poseidon.external_linear_lazy)
theorem round_link13_QPlain : PV_B3P_Link_poseidon_full_round source_round13_QPlain :=
  funext fun state => funext fun constants1 => (full_round_source_fold11 state constants1).symm
#print axioms round_link13_QPlain
end PV_B3P_Binding13227
