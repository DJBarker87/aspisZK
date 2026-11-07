import RSL_TX2_233
import NMS_CloneRef234
set_option autoImplicit false
namespace NMS_CloneRef233
open RSL RSL.TX2_233

/- Canonical RSL reference with explicit general ProgramError clone stops.
Only getter interpretation and recursively corrected child references differ.
No normal result, payload, ordered effect, Box or original input is erased. -/
/-- Body after the seven-account destructuring, lines 246-334. -/
def body (L : PoolLib) (D : DeployedIds) (a : Args)
    (p m c l r e v : OwnedAccount) : RS Authenticated :=
  let pool := a.pool_program
  RS.seq (RS.ofExcept (readonlyBuffer p)) <|
  RS.seq (NMS_GeneralGetters.checkpoint v a.verifier_program false) <|
  RS.seq (RS.ofExcept (readonlyAccount m pool)) <|
  RS.seq (RS.ofExcept (readonlyAccount c pool)) <|
  RS.seq (RS.ofExcept (readonlyAccount l pool)) <|
  RS.seq (RS.ofExcept (requireDistinct [p, m, c, l, r, e, v])) <|
  -- master (lines 261-275); `||` short-circuits the PDA syscall
  RS.bind (NMS_GeneralGetters.data m) fun mdata =>
  RS.bind (decodeMasterBox L mdata) fun master =>
  RS.seq (if decide (master.identity.pool ≠ m.key) || master.initialized_lane_mask != ALL_LANES_MASK
          then RS.throw .invalidAccountData
          else RS.bind (pdaOrErr [SEED_MASTER, master.identity.asset_mint.bytes, [master.bump]] pool)
                 fun k => RS.check (decide (k ≠ m.key)) .invalidAccountData) <|
  -- registry (lines 276-284): OPEN child TX2:234 at SAME arguments
  RS.seq (Spec.call TX2_234.Domain (NMS_CloneRef234.Ref L D)
            ⟨a.verifier_program, pool, m, master, r, e, a.current_slot⟩) <|
  -- checkpoint (lines 286-301)
  RS.bind (NMS_GeneralGetters.data c) fun cdata =>
  RS.bind (decodeCheckpointBox L cdata) fun ck =>
  RS.seq (if decide (ck.master ≠ m.key)
             || decide (ck.deployment_domain ≠ master.identity.deployment_domain)
          then RS.throw .invalidAccountData
          else RS.bind (pdaOrErr [SEED_CHECKPOINT, m.key.bytes, u64le ck.checkpoint_sequence,
                                  [ck.bump]] pool)
                 fun k => RS.check (decide (k ≠ c.key)) .invalidAccountData) <|
  -- selected lane (lines 302-317): OPEN child TX2:217 at SAME argument
  RS.bind (NMS_GeneralGetters.data l) fun ldata =>
  RS.bind (Spec.call TX2_217.Domain TX2_217.Ref ldata) fun lane =>
  RS.seq (if decide (lane.master ≠ m.key) || lane.lane_id != a.output_lane
          then RS.throw .invalidAccountData
          else RS.bind (pdaOrErr [SEED_LANE, m.key.bytes, [a.output_lane], [lane.bump]] pool)
                 fun k => RS.check (decide (k ≠ l.key)) .invalidAccountData) <|
  -- live snapshot Box (lines 318-325) and the returned owner (326-334)
  RS.seq (RS.lift Spec.alloc) <|
  RS.pure { master_account := m.key, checkpoint_account := c.key,
            selected_lane_account := l.key, master := master, checkpoint := ck,
            selected_lane := lane,
            live_snapshot := { pool := m.key,
                               deployment_domain := master.identity.deployment_domain,
                               sequence := lane.tree.next_leaf_index,
                               next_pair_index := lane.tree.next_leaf_index,
                               current_root := lane.tree.root,
                               frontier := lane.tree.frontier } }

/-- Reference, lines 237-245 then `body`. -/
def Ref (L : PoolLib) (D : DeployedIds) (a : Args) : RS Authenticated :=
  match a.accounts with
  | [p, m, c, l, r, e, v] => body L D a p m c l r e v
  | _ => RS.throw (if a.accounts.length < 7 then .notEnoughAccountKeys else .invalidArgument)


end NMS_CloneRef233
