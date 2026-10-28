from pathlib import Path
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s='''import R1Z.PV_RunJoin_LaneFuns31
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
  PV_RunJoin_Lane31.aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1.PairLeaf
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
'''
for n in range(20):
 s+=f'    rw [index_ok_gen input.membership.siblings {n}#usize (by simp)]\n'
s+='''    rfl
#print axioms complete_result
end R1Z.PV_RunJoin_LaneDenotation31
'''
(L/'PV_RunJoin_LaneDenotation31.lean').write_text(s)
