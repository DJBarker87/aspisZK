import NNH_ValueOk
set_option autoImplicit false
namespace NNH_AuthOkPrefix
open RSL NND_Returned

def tailValue (L : PoolLib) (D : DeployedIds) (a : TX2_233.Args)
 (p m c l r e v : OwnedAccount) (env : Env) : Except ProgramError Authenticated :=
 let pool := a.pool_program
  -- master (lines 261-275); `||` short-circuits the PDA syscall
  ebind (id m.bytes) fun mdata =>
  ebind (option (L.decodeMaster mdata) .invalidAccountData) fun master =>
  eseq (if decide (master.identity.pool ≠ m.key) || master.initialized_lane_mask != ALL_LANES_MASK
          then Except.error .invalidAccountData
          else ebind (NNH_RegistryEval.pdaValue env [SEED_MASTER, master.identity.asset_mint.bytes, [master.bump]] pool)
                 fun k => echeck (decide (k ≠ m.key)) .invalidAccountData) <|
  -- registry (lines 276-284): OPEN child TX2:234 at SAME arguments
  eseq (NNH_RegistryEval.value L D ⟨a.verifier_program, pool, m, master, r, e, a.current_slot⟩ env) <|
  -- checkpoint (lines 286-301)
  ebind (id c.bytes) fun cdata =>
  ebind (option (L.decodeCheckpoint cdata) .invalidAccountData) fun ck =>
  eseq (if decide (ck.master ≠ m.key)
             || decide (ck.deployment_domain ≠ master.identity.deployment_domain)
          then Except.error .invalidAccountData
          else ebind (NNH_RegistryEval.pdaValue env [SEED_CHECKPOINT, m.key.bytes, u64le ck.checkpoint_sequence,
                                  [ck.bump]] pool)
                 fun k => echeck (decide (k ≠ c.key)) .invalidAccountData) <|
  -- selected lane (lines 302-317): OPEN child TX2:217 at SAME argument
  ebind (id l.bytes) fun ldata =>
  ebind (NND_LaneReturned.value ldata) fun lane =>
  eseq (if decide (lane.master ≠ m.key) || lane.lane_id != a.output_lane
          then Except.error .invalidAccountData
          else ebind (NNH_RegistryEval.pdaValue env [SEED_LANE, m.key.bytes, [a.output_lane], [lane.bump]] pool)
                 fun k => echeck (decide (k ≠ l.key)) .invalidAccountData) <|
  -- live snapshot Box (lines 318-325) and the returned owner (326-334)
  eseq (Except.ok ()) <|
  Except.ok { master_account := m.key, checkpoint_account := c.key, selected_lane_account := l.key, master := master, checkpoint := ck, selected_lane := lane, live_snapshot := { pool := m.key, deployment_domain := master.identity.deployment_domain, sequence := lane.tree.next_leaf_index, next_pair_index := lane.tree.next_leaf_index, current_root := lane.tree.root, frontier := lane.tree.frontier } }

structure Packet (L : PoolLib) (D : DeployedIds) (a : TX2_233.Args)
 (p m c l r e v : OwnedAccount) (env : Env) (out : Authenticated) : Prop where
 proofGuard : readonlyBuffer p=.ok ()
 checkpointGuard : NNH_ReturnedClone.checkpointValue v a.verifier_program false=.ok ()
 masterGuard : readonlyAccount m a.pool_program=.ok ()
 checkpointOwner : readonlyAccount c a.pool_program=.ok ()
 laneGuard : readonlyAccount l a.pool_program=.ok ()
 distinctGuard : requireDistinct [p,m,c,l,r,e,v]=.ok ()
 tail : tailValue L D a p m c l r e v env=.ok out

theorem produce (L : PoolLib) (D : DeployedIds) (a : TX2_233.Args)
 (p m c l r e v : OwnedAccount) (env : Env) (out : Authenticated)
 (success : NNH_AuthEval.bodyValue L D a p m c l r e v env=.ok out) :
 Packet L D a p m c l r e v env out := by
 unfold NNH_AuthEval.bodyValue at success
 obtain ⟨proofGuard,success⟩ := NNH_ValueOk.seq _ _ out success
 obtain ⟨checkpointGuard,success⟩ := NNH_ValueOk.seq _ _ out success
 obtain ⟨masterGuard,success⟩ := NNH_ValueOk.seq _ _ out success
 obtain ⟨checkpointOwner,success⟩ := NNH_ValueOk.seq _ _ out success
 obtain ⟨laneGuard,success⟩ := NNH_ValueOk.seq _ _ out success
 obtain ⟨distinctGuard,success⟩ := NNH_ValueOk.seq _ _ out success
 exact ⟨proofGuard,checkpointGuard,masterGuard,checkpointOwner,laneGuard,distinctGuard,success⟩
#print axioms produce
end NNH_AuthOkPrefix
