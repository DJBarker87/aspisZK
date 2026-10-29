import PV_B3P_DigestReadSuffix900227
import PV_B3P_LiftHeadEq9227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Success227
set_option autoImplicit false
attribute [local irreducible] reference_terminal.add_digest_binding reference_copy_terminal.Selectors.row reference_terminal.empty_root reference_terminal.digest227 reference_terminal.bounded_append_carry

theorem digest_source_factor9 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    reference_terminal.public_digest_lanes public1 openings selectors =
      digest_suffix_00 public1 openings selectors := by
  unfold reference_terminal.public_digest_lanes
  conv_rhs => rw [digest_suffix_00_equation]; simp only [digest_stage_00,digest_assoc,lift,bind_tc_ok]
  apply lift_head_equal9 (Usize.wrapping_mul 56#usize 16#usize)
  apply lift_head_equal9 (Usize.wrapping_add (Usize.wrapping_mul 56#usize 16#usize) 11#usize)
  apply bind_equal9
  intro head_0_0
  apply bind_equal9
  intro head_0_1
  conv_rhs => rw [digest_suffix_01_equation]; simp only [digest_stage_01,digest_assoc,lift,bind_tc_ok]
  apply lift_head_equal9 (Usize.wrapping_mul 26#usize 16#usize)
  apply lift_head_equal9 (Usize.wrapping_add (Usize.wrapping_mul 26#usize 16#usize) 11#usize)
  apply bind_equal9
  intro head_1_0
  apply bind_equal9
  intro head_1_1
  conv_rhs => rw [digest_suffix_02_equation,recipient_stage_action9]
  apply recipient_equal9 public1.recipient head_1_1 openings.z selectors
  intro recipient_output
  conv_rhs => rw [digest_suffix_03_equation]; simp only [digest_stage_03,digest_assoc,lift,bind_tc_ok]
  apply lift_head_equal9 (Usize.wrapping_mul 32#usize 16#usize)
  apply lift_head_equal9 (Usize.wrapping_add (Usize.wrapping_mul 32#usize 16#usize) 11#usize)
  apply bind_equal9
  intro head_3_0
  apply bind_equal9
  intro head_3_1
  conv_rhs => rw [digest_suffix_04_equation]; simp only [digest_stage_04,digest_assoc,lift,bind_tc_ok]
  apply lift_head_equal9 (Usize.wrapping_add 34#usize 0#usize)
  apply lift_head_equal9 (U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 0#u32)
  apply lift_head_equal9 ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 0#u32) &&& 1#u64)
  conv_rhs => change (frontier_primitive9 head_3_1 openings.z selectors public1.transition.live_snapshot.frontier 0#usize (Usize.wrapping_add 34#usize 0#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 0#u32) &&& 1#u64) >>= digest_suffix_05 public1 openings selectors); rw [frontier_primitive_bind9]
  apply frontier_equal9 head_3_1 openings.z selectors public1.transition.live_snapshot.frontier 0#usize (Usize.wrapping_add 34#usize 0#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 0#u32) &&& 1#u64)
  intro frontier_output_4
  conv_rhs => rw [digest_suffix_05_equation]; simp only [digest_stage_05,digest_assoc,lift,bind_tc_ok]
  apply lift_head_equal9 (Usize.wrapping_add 34#usize 1#usize)
  apply lift_head_equal9 (U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 1#u32)
  apply lift_head_equal9 ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 1#u32) &&& 1#u64)
  conv_rhs => change (frontier_primitive9 frontier_output_4 openings.z selectors public1.transition.live_snapshot.frontier 1#usize (Usize.wrapping_add 34#usize 1#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 1#u32) &&& 1#u64) >>= digest_suffix_06 public1 openings selectors); rw [frontier_primitive_bind9]
  apply frontier_equal9 frontier_output_4 openings.z selectors public1.transition.live_snapshot.frontier 1#usize (Usize.wrapping_add 34#usize 1#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 1#u32) &&& 1#u64)
  intro frontier_output_5
  conv_rhs => rw [digest_suffix_06_equation]; simp only [digest_stage_06,digest_assoc,lift,bind_tc_ok]
  apply lift_head_equal9 (Usize.wrapping_add 34#usize 2#usize)
  apply lift_head_equal9 (U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 2#u32)
  apply lift_head_equal9 ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 2#u32) &&& 1#u64)
  conv_rhs => change (frontier_primitive9 frontier_output_5 openings.z selectors public1.transition.live_snapshot.frontier 2#usize (Usize.wrapping_add 34#usize 2#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 2#u32) &&& 1#u64) >>= digest_suffix_07 public1 openings selectors); rw [frontier_primitive_bind9]
  apply frontier_equal9 frontier_output_5 openings.z selectors public1.transition.live_snapshot.frontier 2#usize (Usize.wrapping_add 34#usize 2#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 2#u32) &&& 1#u64)
  intro frontier_output_6
  conv_rhs => rw [digest_suffix_07_equation]; simp only [digest_stage_07,digest_assoc,lift,bind_tc_ok]
  apply lift_head_equal9 (Usize.wrapping_add 34#usize 3#usize)
  apply lift_head_equal9 (U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 3#u32)
  apply lift_head_equal9 ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 3#u32) &&& 1#u64)
  conv_rhs => change (frontier_primitive9 frontier_output_6 openings.z selectors public1.transition.live_snapshot.frontier 3#usize (Usize.wrapping_add 34#usize 3#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 3#u32) &&& 1#u64) >>= digest_suffix_08 public1 openings selectors); rw [frontier_primitive_bind9]
  apply frontier_equal9 frontier_output_6 openings.z selectors public1.transition.live_snapshot.frontier 3#usize (Usize.wrapping_add 34#usize 3#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 3#u32) &&& 1#u64)
  intro frontier_output_7
  conv_rhs => rw [digest_suffix_08_equation]; simp only [digest_stage_08,digest_assoc,lift,bind_tc_ok]
  apply lift_head_equal9 (Usize.wrapping_add 34#usize 4#usize)
  apply lift_head_equal9 (U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 4#u32)
  apply lift_head_equal9 ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 4#u32) &&& 1#u64)
  conv_rhs => change (frontier_primitive9 frontier_output_7 openings.z selectors public1.transition.live_snapshot.frontier 4#usize (Usize.wrapping_add 34#usize 4#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 4#u32) &&& 1#u64) >>= digest_suffix_09 public1 openings selectors); rw [frontier_primitive_bind9]
  apply frontier_equal9 frontier_output_7 openings.z selectors public1.transition.live_snapshot.frontier 4#usize (Usize.wrapping_add 34#usize 4#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 4#u32) &&& 1#u64)
  intro frontier_output_8
  conv_rhs => rw [digest_suffix_09_equation]; simp only [digest_stage_09,digest_assoc,lift,bind_tc_ok]
  apply lift_head_equal9 (Usize.wrapping_add 34#usize 5#usize)
  apply lift_head_equal9 (U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 5#u32)
  apply lift_head_equal9 ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 5#u32) &&& 1#u64)
  conv_rhs => change (frontier_primitive9 frontier_output_8 openings.z selectors public1.transition.live_snapshot.frontier 5#usize (Usize.wrapping_add 34#usize 5#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 5#u32) &&& 1#u64) >>= digest_suffix_10 public1 openings selectors); rw [frontier_primitive_bind9]
  apply frontier_equal9 frontier_output_8 openings.z selectors public1.transition.live_snapshot.frontier 5#usize (Usize.wrapping_add 34#usize 5#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 5#u32) &&& 1#u64)
  intro frontier_output_9
  conv_rhs => rw [digest_suffix_10_equation]; simp only [digest_stage_10,digest_assoc,lift,bind_tc_ok]
  apply lift_head_equal9 (Usize.wrapping_add 34#usize 6#usize)
  apply lift_head_equal9 (U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 6#u32)
  apply lift_head_equal9 ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 6#u32) &&& 1#u64)
  conv_rhs => change (frontier_primitive9 frontier_output_9 openings.z selectors public1.transition.live_snapshot.frontier 6#usize (Usize.wrapping_add 34#usize 6#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 6#u32) &&& 1#u64) >>= digest_suffix_11 public1 openings selectors); rw [frontier_primitive_bind9]
  apply frontier_equal9 frontier_output_9 openings.z selectors public1.transition.live_snapshot.frontier 6#usize (Usize.wrapping_add 34#usize 6#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 6#u32) &&& 1#u64)
  intro frontier_output_10
  conv_rhs => rw [digest_suffix_11_equation]; simp only [digest_stage_11,digest_assoc,lift,bind_tc_ok]
  apply lift_head_equal9 (Usize.wrapping_add 34#usize 7#usize)
  apply lift_head_equal9 (U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 7#u32)
  apply lift_head_equal9 ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 7#u32) &&& 1#u64)
  conv_rhs => change (frontier_primitive9 frontier_output_10 openings.z selectors public1.transition.live_snapshot.frontier 7#usize (Usize.wrapping_add 34#usize 7#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 7#u32) &&& 1#u64) >>= digest_suffix_12 public1 openings selectors); rw [frontier_primitive_bind9]
  apply frontier_equal9 frontier_output_10 openings.z selectors public1.transition.live_snapshot.frontier 7#usize (Usize.wrapping_add 34#usize 7#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 7#u32) &&& 1#u64)
  intro frontier_output_11
  conv_rhs => rw [digest_suffix_12_equation]; simp only [digest_stage_12,digest_assoc,lift,bind_tc_ok]
  apply lift_head_equal9 (Usize.wrapping_add 34#usize 8#usize)
  apply lift_head_equal9 (U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 8#u32)
  apply lift_head_equal9 ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 8#u32) &&& 1#u64)
  conv_rhs => change (frontier_primitive9 frontier_output_11 openings.z selectors public1.transition.live_snapshot.frontier 8#usize (Usize.wrapping_add 34#usize 8#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 8#u32) &&& 1#u64) >>= digest_suffix_13 public1 openings selectors); rw [frontier_primitive_bind9]
  apply frontier_equal9 frontier_output_11 openings.z selectors public1.transition.live_snapshot.frontier 8#usize (Usize.wrapping_add 34#usize 8#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 8#u32) &&& 1#u64)
  intro frontier_output_12
  conv_rhs => rw [digest_suffix_13_equation]; simp only [digest_stage_13,digest_assoc,lift,bind_tc_ok]
  apply lift_head_equal9 (Usize.wrapping_add 34#usize 9#usize)
  apply lift_head_equal9 (U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 9#u32)
  apply lift_head_equal9 ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 9#u32) &&& 1#u64)
  conv_rhs => change (frontier_primitive9 frontier_output_12 openings.z selectors public1.transition.live_snapshot.frontier 9#usize (Usize.wrapping_add 34#usize 9#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 9#u32) &&& 1#u64) >>= digest_suffix_14 public1 openings selectors); rw [frontier_primitive_bind9]
  apply frontier_equal9 frontier_output_12 openings.z selectors public1.transition.live_snapshot.frontier 9#usize (Usize.wrapping_add 34#usize 9#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 9#u32) &&& 1#u64)
  intro frontier_output_13
  conv_rhs => rw [digest_suffix_14_equation]; simp only [digest_stage_14,digest_assoc,lift,bind_tc_ok]
  apply lift_head_equal9 (Usize.wrapping_add 34#usize 10#usize)
  apply lift_head_equal9 (U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 10#u32)
  apply lift_head_equal9 ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 10#u32) &&& 1#u64)
  conv_rhs => change (frontier_primitive9 frontier_output_13 openings.z selectors public1.transition.live_snapshot.frontier 10#usize (Usize.wrapping_add 34#usize 10#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 10#u32) &&& 1#u64) >>= digest_suffix_15 public1 openings selectors); rw [frontier_primitive_bind9]
  apply frontier_equal9 frontier_output_13 openings.z selectors public1.transition.live_snapshot.frontier 10#usize (Usize.wrapping_add 34#usize 10#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 10#u32) &&& 1#u64)
  intro frontier_output_14
  conv_rhs => rw [digest_suffix_15_equation]; simp only [digest_stage_15,digest_assoc,lift,bind_tc_ok]
  apply lift_head_equal9 (Usize.wrapping_add 34#usize 11#usize)
  apply lift_head_equal9 (U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 11#u32)
  apply lift_head_equal9 ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 11#u32) &&& 1#u64)
  conv_rhs => change (frontier_primitive9 frontier_output_14 openings.z selectors public1.transition.live_snapshot.frontier 11#usize (Usize.wrapping_add 34#usize 11#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 11#u32) &&& 1#u64) >>= digest_suffix_16 public1 openings selectors); rw [frontier_primitive_bind9]
  apply frontier_equal9 frontier_output_14 openings.z selectors public1.transition.live_snapshot.frontier 11#usize (Usize.wrapping_add 34#usize 11#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 11#u32) &&& 1#u64)
  intro frontier_output_15
  conv_rhs => rw [digest_suffix_16_equation]; simp only [digest_stage_16,digest_assoc,lift,bind_tc_ok]
  apply lift_head_equal9 (Usize.wrapping_add 34#usize 12#usize)
  apply lift_head_equal9 (U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 12#u32)
  apply lift_head_equal9 ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 12#u32) &&& 1#u64)
  conv_rhs => change (frontier_primitive9 frontier_output_15 openings.z selectors public1.transition.live_snapshot.frontier 12#usize (Usize.wrapping_add 34#usize 12#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 12#u32) &&& 1#u64) >>= digest_suffix_17 public1 openings selectors); rw [frontier_primitive_bind9]
  apply frontier_equal9 frontier_output_15 openings.z selectors public1.transition.live_snapshot.frontier 12#usize (Usize.wrapping_add 34#usize 12#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 12#u32) &&& 1#u64)
  intro frontier_output_16
  conv_rhs => rw [digest_suffix_17_equation]; simp only [digest_stage_17,digest_assoc,lift,bind_tc_ok]
  apply lift_head_equal9 (Usize.wrapping_add 34#usize 13#usize)
  apply lift_head_equal9 (U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 13#u32)
  apply lift_head_equal9 ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 13#u32) &&& 1#u64)
  conv_rhs => change (frontier_primitive9 frontier_output_16 openings.z selectors public1.transition.live_snapshot.frontier 13#usize (Usize.wrapping_add 34#usize 13#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 13#u32) &&& 1#u64) >>= digest_suffix_18 public1 openings selectors); rw [frontier_primitive_bind9]
  apply frontier_equal9 frontier_output_16 openings.z selectors public1.transition.live_snapshot.frontier 13#usize (Usize.wrapping_add 34#usize 13#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 13#u32) &&& 1#u64)
  intro frontier_output_17
  conv_rhs => rw [digest_suffix_18_equation]; simp only [digest_stage_18,digest_assoc,lift,bind_tc_ok]
  apply lift_head_equal9 (Usize.wrapping_add 34#usize 14#usize)
  apply lift_head_equal9 (U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 14#u32)
  apply lift_head_equal9 ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 14#u32) &&& 1#u64)
  conv_rhs => change (frontier_primitive9 frontier_output_17 openings.z selectors public1.transition.live_snapshot.frontier 14#usize (Usize.wrapping_add 34#usize 14#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 14#u32) &&& 1#u64) >>= digest_suffix_19 public1 openings selectors); rw [frontier_primitive_bind9]
  apply frontier_equal9 frontier_output_17 openings.z selectors public1.transition.live_snapshot.frontier 14#usize (Usize.wrapping_add 34#usize 14#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 14#u32) &&& 1#u64)
  intro frontier_output_18
  conv_rhs => rw [digest_suffix_19_equation]; simp only [digest_stage_19,digest_assoc,lift,bind_tc_ok]
  apply lift_head_equal9 (Usize.wrapping_add 34#usize 15#usize)
  apply lift_head_equal9 (U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 15#u32)
  apply lift_head_equal9 ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 15#u32) &&& 1#u64)
  conv_rhs => change (frontier_primitive9 frontier_output_18 openings.z selectors public1.transition.live_snapshot.frontier 15#usize (Usize.wrapping_add 34#usize 15#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 15#u32) &&& 1#u64) >>= digest_suffix_20 public1 openings selectors); rw [frontier_primitive_bind9]
  apply frontier_equal9 frontier_output_18 openings.z selectors public1.transition.live_snapshot.frontier 15#usize (Usize.wrapping_add 34#usize 15#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 15#u32) &&& 1#u64)
  intro frontier_output_19
  conv_rhs => rw [digest_suffix_20_equation]; simp only [digest_stage_20,digest_assoc,lift,bind_tc_ok]
  apply lift_head_equal9 (Usize.wrapping_add 34#usize 16#usize)
  apply lift_head_equal9 (U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 16#u32)
  apply lift_head_equal9 ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 16#u32) &&& 1#u64)
  conv_rhs => change (frontier_primitive9 frontier_output_19 openings.z selectors public1.transition.live_snapshot.frontier 16#usize (Usize.wrapping_add 34#usize 16#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 16#u32) &&& 1#u64) >>= digest_suffix_21 public1 openings selectors); rw [frontier_primitive_bind9]
  apply frontier_equal9 frontier_output_19 openings.z selectors public1.transition.live_snapshot.frontier 16#usize (Usize.wrapping_add 34#usize 16#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 16#u32) &&& 1#u64)
  intro frontier_output_20
  conv_rhs => rw [digest_suffix_21_equation]; simp only [digest_stage_21,digest_assoc,lift,bind_tc_ok]
  apply lift_head_equal9 (Usize.wrapping_add 34#usize 17#usize)
  apply lift_head_equal9 (U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 17#u32)
  apply lift_head_equal9 ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 17#u32) &&& 1#u64)
  conv_rhs => change (frontier_primitive9 frontier_output_20 openings.z selectors public1.transition.live_snapshot.frontier 17#usize (Usize.wrapping_add 34#usize 17#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 17#u32) &&& 1#u64) >>= digest_suffix_22 public1 openings selectors); rw [frontier_primitive_bind9]
  apply frontier_equal9 frontier_output_20 openings.z selectors public1.transition.live_snapshot.frontier 17#usize (Usize.wrapping_add 34#usize 17#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 17#u32) &&& 1#u64)
  intro frontier_output_21
  conv_rhs => rw [digest_suffix_22_equation]; simp only [digest_stage_22,digest_assoc,lift,bind_tc_ok]
  apply lift_head_equal9 (Usize.wrapping_add 34#usize 18#usize)
  apply lift_head_equal9 (U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 18#u32)
  apply lift_head_equal9 ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 18#u32) &&& 1#u64)
  conv_rhs => change (frontier_primitive9 frontier_output_21 openings.z selectors public1.transition.live_snapshot.frontier 18#usize (Usize.wrapping_add 34#usize 18#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 18#u32) &&& 1#u64) >>= digest_suffix_23 public1 openings selectors); rw [frontier_primitive_bind9]
  apply frontier_equal9 frontier_output_21 openings.z selectors public1.transition.live_snapshot.frontier 18#usize (Usize.wrapping_add 34#usize 18#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 18#u32) &&& 1#u64)
  intro frontier_output_22
  conv_rhs => rw [digest_suffix_23_equation]; simp only [digest_stage_23,digest_assoc,lift,bind_tc_ok]
  apply lift_head_equal9 (Usize.wrapping_add 34#usize 19#usize)
  apply lift_head_equal9 (U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 19#u32)
  apply lift_head_equal9 ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 19#u32) &&& 1#u64)
  conv_rhs => change (frontier_primitive9 frontier_output_22 openings.z selectors public1.transition.live_snapshot.frontier 19#usize (Usize.wrapping_add 34#usize 19#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 19#u32) &&& 1#u64) >>= digest_suffix_24 public1 openings selectors); rw [frontier_primitive_bind9]
  apply frontier_equal9 frontier_output_22 openings.z selectors public1.transition.live_snapshot.frontier 19#usize (Usize.wrapping_add 34#usize 19#usize) ((U64.wrapping_shr public1.transition.live_snapshot.next_pair_index 19#u32) &&& 1#u64)
  intro frontier_output_23
  rfl

#print axioms digest_source_factor9

theorem public_digest_read_binding9 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    reference_terminal.public_digest_lanes public1 openings selectors =
      digest_direct_suffix9_00 public1 openings selectors :=
  (digest_source_factor9 public1 openings selectors).trans
    (digest_suffix_read_binding9_00 public1 openings selectors)
#print axioms public_digest_read_binding9
end PV_B3P_Binding9227
