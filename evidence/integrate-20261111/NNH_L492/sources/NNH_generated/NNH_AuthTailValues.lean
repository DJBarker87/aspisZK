import NNH_AuthOkPrefix
import NNH_OptionOk
set_option autoImplicit false
namespace NNH_AuthTailValues
open RSL NND_Returned
def laneValue (L : PoolLib) (D : DeployedIds) (a : TX2_233.Args)
 (p m c l r e v : OwnedAccount) (env : Env) (master : Master) (ck : Checkpoint) : Except ProgramError Authenticated :=
  let pool := a.pool_program
  ebind (id l.bytes) fun ldata =>
  ebind (NND_LaneReturned.value ldata) fun lane =>
  eseq (if decide (lane.master ≠ m.key) || lane.lane_id != a.output_lane
          then Except.error .invalidAccountData
          else ebind (NNH_RegistryEval.pdaValue env [SEED_LANE, m.key.bytes, [a.output_lane], [lane.bump]] pool)
                 fun k => echeck (decide (k ≠ l.key)) .invalidAccountData) <|
  -- live snapshot Box (lines 318-325) and the returned owner (326-334)
  eseq (Except.ok ()) <|
  Except.ok { master_account := m.key, checkpoint_account := c.key, selected_lane_account := l.key, master := master, checkpoint := ck, selected_lane := lane, live_snapshot := { pool := m.key, deployment_domain := master.identity.deployment_domain, sequence := lane.tree.next_leaf_index, next_pair_index := lane.tree.next_leaf_index, current_root := lane.tree.root, frontier := lane.tree.frontier } }

def checkpointValue (L : PoolLib) (D : DeployedIds) (a : TX2_233.Args)
 (p m c l r e v : OwnedAccount) (env : Env) (master : Master) : Except ProgramError Authenticated :=
  let pool := a.pool_program
  ebind (id c.bytes) fun cdata =>
  ebind (option (L.decodeCheckpoint cdata) .invalidAccountData) fun ck =>
  eseq (if decide (ck.master ≠ m.key)
             || decide (ck.deployment_domain ≠ master.identity.deployment_domain)
          then Except.error .invalidAccountData
          else ebind (NNH_RegistryEval.pdaValue env [SEED_CHECKPOINT, m.key.bytes, u64le ck.checkpoint_sequence,
                                  [ck.bump]] pool)
                 fun k => echeck (decide (k ≠ c.key)) .invalidAccountData) <|
  laneValue L D a p m c l r e v env master ck

def masterValue (L : PoolLib) (D : DeployedIds) (a : TX2_233.Args)
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
  checkpointValue L D a p m c l r e v env master


theorem factor (L : PoolLib) (D : DeployedIds) (a : TX2_233.Args)
 (p m c l r e v : OwnedAccount) (env : Env) : NNH_AuthOkPrefix.tailValue L D a p m c l r e v env =
 masterValue L D a p m c l r e v env := by rfl
#print axioms factor
end NNH_AuthTailValues
