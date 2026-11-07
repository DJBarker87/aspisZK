import NMX_CanonicalTarget
import NMS_RSLRefine
set_option autoImplicit false
namespace NMX_RSL233Replay
open RSL NMS_RSLRefine
/-- Canonical source-order reference with full native observations at the two
OPEN child occurrences. This is relational source support until the actual
emitted-body interpretation and CLOSED carrier adapters are installed. -/
def replayBody (L : PoolLib) (D : DeployedIds)
    (laneNative : Bytes → Env → Obs (Except ProgramError LaneState))
    (registryNative : TX2_234.Args → Env → Obs (Except ProgramError Unit))
    (a : TX2_233.Args)
    (p m c l r e v : OwnedAccount) : RS Authenticated :=
  let pool := a.pool_program
  RS.seq (RS.ofExcept (readonlyBuffer p)) <|
  RS.seq (RS.ofExcept (verifierCheckpoint v a.verifier_program false)) <|
  RS.seq (RS.ofExcept (readonlyAccount m pool)) <|
  RS.seq (RS.ofExcept (readonlyAccount c pool)) <|
  RS.seq (RS.ofExcept (readonlyAccount l pool)) <|
  RS.seq (RS.ofExcept (requireDistinct [p, m, c, l, r, e, v])) <|
  -- master (lines 261-275); `||` short-circuits the PDA syscall
  RS.bind (RS.ofExcept m.data) fun mdata =>
  RS.bind (decodeMasterBox L mdata) fun master =>
  RS.seq (if decide (master.identity.pool ≠ m.key) || master.initialized_lane_mask != ALL_LANES_MASK
          then RS.throw .invalidAccountData
          else RS.bind (pdaOrErr [SEED_MASTER, master.identity.asset_mint.bytes, [master.bump]] pool)
                 fun k => RS.check (decide (k ≠ m.key)) .invalidAccountData) <|
  -- registry (lines 276-284): OPEN child TX2:234 at SAME arguments
  RS.seq (NMS_RSLRefine.observed registryNative
            ⟨a.verifier_program, pool, m, master, r, e, a.current_slot⟩) <|
  -- checkpoint (lines 286-301)
  RS.bind (RS.ofExcept c.data) fun cdata =>
  RS.bind (decodeCheckpointBox L cdata) fun ck =>
  RS.seq (if decide (ck.master ≠ m.key)
             || decide (ck.deployment_domain ≠ master.identity.deployment_domain)
          then RS.throw .invalidAccountData
          else RS.bind (pdaOrErr [SEED_CHECKPOINT, m.key.bytes, u64le ck.checkpoint_sequence,
                                  [ck.bump]] pool)
                 fun k => RS.check (decide (k ≠ c.key)) .invalidAccountData) <|
  -- selected lane (lines 302-317): OPEN child TX2:217 at SAME argument
  RS.bind (RS.ofExcept l.data) fun ldata =>
  RS.bind (NMS_RSLRefine.observed laneNative ldata) fun lane =>
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


theorem body_fold (L : PoolLib) (D : DeployedIds)
 (laneNative : Bytes → Env → Obs (Except ProgramError LaneState))
 (registryNative : TX2_234.Args → Env → Obs (Except ProgramError Unit))
 (lanePacket : TX2_217.RowSpec_217 laneNative)
 (registryPacket : TX2_234.RowSpec_234 L D registryNative)
 (a : TX2_233.Args) (p m c l r e v : OwnedAccount) :
 Refines (replayBody L D laneNative registryNative a p m c l r e v)
  (TX2_233.body L D a p m c l r e v) := by
 unfold replayBody TX2_233.body
 apply rsseq (refl _)
 apply rsseq (refl _)
 apply rsseq (refl _)
 apply rsseq (refl _)
 apply rsseq (refl _)
 apply rsseq (refl _)
 apply rsbind (refl _)
 intro mdata
 apply rsbind (refl _)
 intro master
 apply rsseq (refl _)
 apply rsseq (call TX2_234.Domain (TX2_234.Ref L D) registryNative registryPacket _ trivial)
 apply rsbind (refl _)
 intro cdata
 apply rsbind (refl _)
 intro ck
 apply rsseq (refl _)
 apply rsbind (refl _)
 intro ldata
 apply rsbind (call TX2_217.Domain TX2_217.Ref laneNative lanePacket _ trivial)
 intro lane
 exact refl _

#print axioms body_fold
end NMX_RSL233Replay
