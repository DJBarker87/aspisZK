import NNH_AuthCheckpointCut
set_option autoImplicit false
namespace NNH_AuthLaneCut
open RSL NND_Returned

structure Packet (L : PoolLib) (D : DeployedIds) (a : TX2_233.Args)
 (p m c l r e v : OwnedAccount) (env : Env) (master : Master) (ck : Checkpoint) (out : Authenticated) where
 data : Bytes
 data_ok : l.bytes=.ok data
 lane : LaneState
 decode_ok : NND_LaneReturned.value data=.ok lane
 guard_ok : (decide (lane.master ≠ m.key) || lane.lane_id != a.output_lane)=false
 pda_ok : env.pda [SEED_LANE,m.key.bytes,[a.output_lane],[lane.bump]] a.pool_program=some l.key
 output : out={ master_account := m.key, checkpoint_account := c.key, selected_lane_account := l.key, master := master, checkpoint := ck, selected_lane := lane, live_snapshot := {pool := m.key,deployment_domain := master.identity.deployment_domain, sequence := lane.tree.next_leaf_index,next_pair_index := lane.tree.next_leaf_index, current_root := lane.tree.root,frontier := lane.tree.frontier} }

theorem produce (L : PoolLib) (D : DeployedIds) (a : TX2_233.Args)
 (p m c l r e v : OwnedAccount) (env : Env) (master : Master) (ck : Checkpoint) (out : Authenticated)
 (success : NNH_AuthTailValues.laneValue L D a p m c l r e v env master ck=.ok out) :
 Nonempty (Packet L D a p m c l r e v env master ck out) := by
 unfold NNH_AuthTailValues.laneValue at success
 obtain ⟨data,data_ok,success⟩ := NNH_ValueOk.bind _ _ out success
 obtain ⟨lane,decode,success⟩ := NNH_ValueOk.bind _ _ out success
 obtain ⟨guard,success⟩ := NNH_ValueOk.seq _ _ out success
 obtain ⟨guard_ok,pda_ok⟩ := NNH_PdaOk.guard _ _ _ _ _ guard
 exact ⟨⟨data,data_ok,lane,decode,guard_ok,pda_ok,(Except.ok.inj success).symm⟩⟩
#print axioms produce
end NNH_AuthLaneCut
