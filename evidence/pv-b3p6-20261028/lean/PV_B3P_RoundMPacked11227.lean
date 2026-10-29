import PV_B3P_RoundMPacked10227
import PV_B3P_SixteenFinish11227
namespace PV_B3P_Binding11227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding10227
set_option autoImplicit false
attribute [local irreducible] round_m_step10 reference_poseidon.external_linear_packed
theorem full_round_m31_constants_packed_source_fold11 (state : RoundState10) (constants1 : Array U32 16#usize) :
    reference_poseidon.full_round_m31_constants_packed state constants1 = (PV_B3P_Ordered227.fold (round_m_step10 constants1) [0#usize, 1#usize, 2#usize, 3#usize, 4#usize, 5#usize, 6#usize, 7#usize, 8#usize, 9#usize, 10#usize, 11#usize, 12#usize, 13#usize, 14#usize, 15#usize] state >>= reference_poseidon.external_linear_packed) := by
  rw [full_round_m31_constants_packed_body_binding10]
  unfold round_m_group10_00 round_m_folded10_04 round_m_folded10_08 round_m_folded10_12 round_m_group10_04 round_m_group10_08 round_m_group10_12
  exact sixteen_finish11 (round_m_step10 constants1) state reference_poseidon.external_linear_packed
#print axioms full_round_m31_constants_packed_source_fold11
end PV_B3P_Binding11227
