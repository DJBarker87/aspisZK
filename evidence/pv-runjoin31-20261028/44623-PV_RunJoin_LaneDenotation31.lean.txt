import R1Z.PV_RunJoin_LaneFuns31
import R1Z.PV_RunJoin_LaneRecipe31
import R1Z.PV_RunJoin_BindCongruence
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LaneDenotation31
open Aeneas Aeneas.Std Result
open PV_RunJoin_LaneFold31 PV_RunJoin_LaneRecipe31
abbrev Pair := PV_RunJoin_Lane31.aspis_statement.pool_v1.pair_trace.PoolV1PairInputNoteWitnessV1
variable [BuilderForestAdmissionPort.ExternalLinear]

def sibling (input : Pair) (level : Nat) : Digest := input.membership.siblings.val[level]!
def reverse (input : Pair) (level : Nat) : Bool :=
  let count := U32.ofNatCore (level%20) (by have := Nat.mod_lt level (by decide : 0<20); omega)
  (U32.wrapping_shr input.membership.index count &&& 1#u32) != 0#u32

def model (input : Pair) := recipe
  (PV_RunJoin_Lane31.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.leaf_digest input.pair_leaf)
  PV_RunJoin_Lane31.aspis_statement.pool_v1.pair_trace.PV31_PoolV1PairTraceErrorV1.PairLeaf
  PV_RunJoin_Lane31.aspis_statement.pool_v1.format.pool_v1_tree_parent
  (sibling input) (reverse input) (List.range 20)

attribute [local irreducible] BuilderForestAdmissionPort.pool_v1.format.pool_v1_tree_parent
  BuilderForestAdmissionPort.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.leaf_digest

theorem complete_result (input : Pair) : PV_RunJoin_Lane31.lane_root input = model input := by
  unfold PV_RunJoin_Lane31.lane_root model recipe
  apply PV_RunJoin_BindCongruence.bind_same
  intro r
  cases r with
  | Err e => rfl
  | Ok d =>
    rw [index_ok_gen input.membership.siblings 0#usize (by simp)]
    rw [index_ok_gen input.membership.siblings 1#usize (by simp)]
    rw [index_ok_gen input.membership.siblings 2#usize (by simp)]
    rw [index_ok_gen input.membership.siblings 3#usize (by simp)]
    rw [index_ok_gen input.membership.siblings 4#usize (by simp)]
    rw [index_ok_gen input.membership.siblings 5#usize (by simp)]
    rw [index_ok_gen input.membership.siblings 6#usize (by simp)]
    rw [index_ok_gen input.membership.siblings 7#usize (by simp)]
    rw [index_ok_gen input.membership.siblings 8#usize (by simp)]
    rw [index_ok_gen input.membership.siblings 9#usize (by simp)]
    rw [index_ok_gen input.membership.siblings 10#usize (by simp)]
    rw [index_ok_gen input.membership.siblings 11#usize (by simp)]
    rw [index_ok_gen input.membership.siblings 12#usize (by simp)]
    rw [index_ok_gen input.membership.siblings 13#usize (by simp)]
    rw [index_ok_gen input.membership.siblings 14#usize (by simp)]
    rw [index_ok_gen input.membership.siblings 15#usize (by simp)]
    rw [index_ok_gen input.membership.siblings 16#usize (by simp)]
    rw [index_ok_gen input.membership.siblings 17#usize (by simp)]
    rw [index_ok_gen input.membership.siblings 18#usize (by simp)]
    rw [index_ok_gen input.membership.siblings 19#usize (by simp)]
    rfl
#print axioms complete_result
end R1Z.PV_RunJoin_LaneDenotation31
