import PV_B3P_RoundQPlain10227
import PV_B3P_RoundQPacked10227
import PV_B3P_RoundMPlain10227
import PV_B3P_RoundMPacked10227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

attribute [local irreducible] round_q_step10 round_m_step10 reference_poseidon.external_linear_lazy reference_poseidon.external_linear_packed

theorem full_round_source_fold10 (state : RoundState10) (constants1 : Array aspis_core.field.QM31 16#usize) :
    reference_poseidon.full_round state constants1 = (do
      let next ← PV_B3P_Ordered227.fold (round_q_step10 constants1) [0#usize, 1#usize, 2#usize, 3#usize, 4#usize, 5#usize, 6#usize, 7#usize, 8#usize, 9#usize, 10#usize, 11#usize, 12#usize, 13#usize, 14#usize, 15#usize] state
      reference_poseidon.external_linear_lazy next) := by
  rw [full_round_body_binding10]
  unfold round_q_group10_00 round_q_folded10_04 round_q_folded10_08 round_q_folded10_12
    round_q_group10_04 round_q_group10_08 round_q_group10_12
  have h := PV_B3P_Ordered227.flatten (round_q_step10 constants1) [[0#usize, 1#usize, 2#usize, 3#usize], [4#usize, 5#usize, 6#usize, 7#usize], [8#usize, 9#usize, 10#usize, 11#usize], [12#usize, 13#usize, 14#usize, 15#usize]] state
  have joined := congrArg (fun result => result >>= reference_poseidon.external_linear_lazy) h
  simpa only [PV_B3P_Ordered227.ranges,PV_B3P_Ordered227.bind_assoc,bind_tc_ok] using joined
#print axioms full_round_source_fold10

theorem full_round_packed_source_fold10 (state : RoundState10) (constants1 : Array aspis_core.field.QM31 16#usize) :
    reference_poseidon.full_round_packed state constants1 = (do
      let next ← PV_B3P_Ordered227.fold (round_q_step10 constants1) [0#usize, 1#usize, 2#usize, 3#usize, 4#usize, 5#usize, 6#usize, 7#usize, 8#usize, 9#usize, 10#usize, 11#usize, 12#usize, 13#usize, 14#usize, 15#usize] state
      reference_poseidon.external_linear_packed next) := by
  rw [full_round_packed_body_binding10]
  unfold round_q_group10_00 round_q_folded10_04 round_q_folded10_08 round_q_folded10_12
    round_q_group10_04 round_q_group10_08 round_q_group10_12
  have h := PV_B3P_Ordered227.flatten (round_q_step10 constants1) [[0#usize, 1#usize, 2#usize, 3#usize], [4#usize, 5#usize, 6#usize, 7#usize], [8#usize, 9#usize, 10#usize, 11#usize], [12#usize, 13#usize, 14#usize, 15#usize]] state
  have joined := congrArg (fun result => result >>= reference_poseidon.external_linear_packed) h
  simpa only [PV_B3P_Ordered227.ranges,PV_B3P_Ordered227.bind_assoc,bind_tc_ok] using joined
#print axioms full_round_packed_source_fold10

theorem full_round_m31_constants_source_fold10 (state : RoundState10) (constants1 : Array U32 16#usize) :
    reference_poseidon.full_round_m31_constants state constants1 = (do
      let next ← PV_B3P_Ordered227.fold (round_m_step10 constants1) [0#usize, 1#usize, 2#usize, 3#usize, 4#usize, 5#usize, 6#usize, 7#usize, 8#usize, 9#usize, 10#usize, 11#usize, 12#usize, 13#usize, 14#usize, 15#usize] state
      reference_poseidon.external_linear_lazy next) := by
  rw [full_round_m31_constants_body_binding10]
  unfold round_m_group10_00 round_m_folded10_04 round_m_folded10_08 round_m_folded10_12
    round_m_group10_04 round_m_group10_08 round_m_group10_12
  have h := PV_B3P_Ordered227.flatten (round_m_step10 constants1) [[0#usize, 1#usize, 2#usize, 3#usize], [4#usize, 5#usize, 6#usize, 7#usize], [8#usize, 9#usize, 10#usize, 11#usize], [12#usize, 13#usize, 14#usize, 15#usize]] state
  have joined := congrArg (fun result => result >>= reference_poseidon.external_linear_lazy) h
  simpa only [PV_B3P_Ordered227.ranges,PV_B3P_Ordered227.bind_assoc,bind_tc_ok] using joined
#print axioms full_round_m31_constants_source_fold10

theorem full_round_m31_constants_packed_source_fold10 (state : RoundState10) (constants1 : Array U32 16#usize) :
    reference_poseidon.full_round_m31_constants_packed state constants1 = (do
      let next ← PV_B3P_Ordered227.fold (round_m_step10 constants1) [0#usize, 1#usize, 2#usize, 3#usize, 4#usize, 5#usize, 6#usize, 7#usize, 8#usize, 9#usize, 10#usize, 11#usize, 12#usize, 13#usize, 14#usize, 15#usize] state
      reference_poseidon.external_linear_packed next) := by
  rw [full_round_m31_constants_packed_body_binding10]
  unfold round_m_group10_00 round_m_folded10_04 round_m_folded10_08 round_m_folded10_12
    round_m_group10_04 round_m_group10_08 round_m_group10_12
  have h := PV_B3P_Ordered227.flatten (round_m_step10 constants1) [[0#usize, 1#usize, 2#usize, 3#usize], [4#usize, 5#usize, 6#usize, 7#usize], [8#usize, 9#usize, 10#usize, 11#usize], [12#usize, 13#usize, 14#usize, 15#usize]] state
  have joined := congrArg (fun result => result >>= reference_poseidon.external_linear_packed) h
  simpa only [PV_B3P_Ordered227.ranges,PV_B3P_Ordered227.bind_assoc,bind_tc_ok] using joined
#print axioms full_round_m31_constants_packed_source_fold10
end PV_B3P_Binding10227
