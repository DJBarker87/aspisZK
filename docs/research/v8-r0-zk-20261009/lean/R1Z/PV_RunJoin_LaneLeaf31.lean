import R1Z.PV_RunJoin_LaneFuns31
import R1Z.PV_RunJoin_LaneField31
import R1Z.PV_RunJoin_PairChecks29
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LaneLeaf31
open Aeneas Aeneas.Std Result R0Z.WriterRefine
abbrev Leaf := PV_RunJoin_Lane31.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1
variable [BuilderForestAdmissionPort.ExternalLinear]

theorem returned (leaf : Leaf) (d : Array U32 8#usize)
    (h : PV_RunJoin_Lane31.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.leaf_digest leaf = ok (.Ok d)) :
    BuilderForestAdmissionPort.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.leaf_digest
      (PV_RunJoin_Lane31.leafToForest leaf) = ok (.Ok d) := by
  unfold PV_RunJoin_Lane31.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.leaf_digest at h
  obtain ⟨r,hr,ht⟩ := BuilderRecordsFields.bind_ok_inv h
  cases r with
  | Err e => cases ht
  | Ok out => cases Result.ok.inj ht; exact hr
#print axioms returned

theorem parent (leaf : BuilderForestAdmissionPort.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1)
    (d : Array U32 8#usize)
    (h : BuilderForestAdmissionPort.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.leaf_digest leaf = ok (.Ok d)) :
    BuilderForestAdmissionPort.pool_v1.format.pool_v1_tree_parent
      leaf.first_commitment leaf.second_commitment = ok d := by
  unfold BuilderForestAdmissionPort.pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.leaf_digest at h
  pv_peel h with r hr
  pv_peel h with cf hf
  cases cf with
  | Continue u =>
    pv_peel h with out ho
    cases Result.ok.inj h
    exact ho
  | Break residual => exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
#print axioms parent

end R1Z.PV_RunJoin_LaneLeaf31
