/-
TX2:233  programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::authenticate_asq8_accounts
Frozen signature (r1_pool_adapter_owned.rs:230):
  fn authenticate_asq8_accounts(verifier_program: &Pubkey, accounts: &[OwnedAccount],
      pool_program: &Pubkey, output_lane: u8, current_slot: u64)
      -> Result<AuthenticatedAsq8Accounts, ProgramError>
Route: emitted body under (bm).
Children: OPEN TX2:234 (RowSpec_234 reference, SAME arguments), OPEN TX2:217
(RowSpec_217 reference); CLOSED require_readonly_buffer (TX2:237),
require_verifier_checkpoint (TX2:238), require_readonly_account (TX2:236),
require_distinct_accounts (TX2:235), OwnedAccount::data/key (TX2:229/231),
decode_master_box (TX2:218), decode_checkpoint_box (TX2:216); PDA syscall slot.
Ledger inventory edges to M31::to_le_bytes (TX2:016) and WideExact::to_le_bytes
(TX2:039) are spurious resolutions of `u64::to_le_bytes` at line 293 (a std
scalar operation under (au)); the spec uses the u64 little-endian encoding.
Own-input domain ((bf)(2)): none.
Effects: ordered PDA syscall events (this body's three and TX2:234's); three
Box allocations inside decode_master_box / decode_checkpoint_box /
decode_lane_from_pool_release and one for live_snapshot, each with its abort
arm at its source position.  No account or return-data write.
Revision 2 (RSL_REVISION2.md): the three `data()?` clones and the `data_len()?`
clone inside require_verifier_checkpoint are allocation sites for a
heap-carrying deferred error (`RS.ofCloned`, NMT-S1 shape).  Domain unchanged.
-/
import RSL_TX2_217
import RSL_TX2_234
set_option autoImplicit false

namespace RSL.TX2_233

structure Args where
  verifier_program : B32
  accounts : List OwnedAccount
  pool_program : B32
  output_lane : UInt8
  current_slot : UInt64

/-- Body after the seven-account destructuring, lines 246-334. -/
def body (L : PoolLib) (D : DeployedIds) (a : Args)
    (p m c l r e v : OwnedAccount) : RS Authenticated :=
  let pool := a.pool_program
  RS.seq (RS.ofExcept (readonlyBuffer p)) <|
  RS.seq (verifierCheckpoint v a.verifier_program false) <|
  RS.seq (RS.ofExcept (readonlyAccount m pool)) <|
  RS.seq (RS.ofExcept (readonlyAccount c pool)) <|
  RS.seq (RS.ofExcept (readonlyAccount l pool)) <|
  RS.seq (RS.ofExcept (requireDistinct [p, m, c, l, r, e, v])) <|
  -- master (lines 261-275); `||` short-circuits the PDA syscall
  RS.bind m.data fun mdata =>
  RS.bind (decodeMasterBox L mdata) fun master =>
  RS.seq (if decide (master.identity.pool ≠ m.key) || master.initialized_lane_mask != ALL_LANES_MASK
          then RS.throw .invalidAccountData
          else RS.bind (pdaOrErr [SEED_MASTER, master.identity.asset_mint.bytes, [master.bump]] pool)
                 fun k => RS.check (decide (k ≠ m.key)) .invalidAccountData) <|
  -- registry (lines 276-284): OPEN child TX2:234 at SAME arguments
  RS.seq (Spec.call TX2_234.Domain (TX2_234.Ref L D)
            ⟨a.verifier_program, pool, m, master, r, e, a.current_slot⟩) <|
  -- checkpoint (lines 286-301)
  RS.bind c.data fun cdata =>
  RS.bind (decodeCheckpointBox L cdata) fun ck =>
  RS.seq (if decide (ck.master ≠ m.key)
             || decide (ck.deployment_domain ≠ master.identity.deployment_domain)
          then RS.throw .invalidAccountData
          else RS.bind (pdaOrErr [SEED_CHECKPOINT, m.key.bytes, u64le ck.checkpoint_sequence,
                                  [ck.bump]] pool)
                 fun k => RS.check (decide (k ≠ c.key)) .invalidAccountData) <|
  -- selected lane (lines 302-317): OPEN child TX2:217 at SAME argument
  RS.bind l.data fun ldata =>
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

/-- Own-input domain: none. -/
def Domain (_a : Args) : Prop := True

def RowSpec_233 (L : PoolLib) (D : DeployedIds)
    (authenticate_asq8_accounts : Args → Env → Obs (Except ProgramError Authenticated)) : Prop :=
  ∀ a env, Domain a → Ref L D a env (authenticate_asq8_accounts a env)

/-! ## Rejection of trivial implementations -/

def withAccounts (as : List OwnedAccount) : Args := ⟨zero32, as, zero32, 0, 0⟩

def acct0 : OwnedAccount := ⟨zero32, zero32, false, false, false, .ok 0, .ok []⟩

theorem rejects_constErr (L : PoolLib) (D : DeployedIds) (e : ProgramError) :
    ¬ RowSpec_233 L D (constErr e) := by
  intro h
  have h0 := h (withAccounts []) env0 trivial
  have h8 := h (withAccounts (List.replicate 8 acct0)) env0 trivial
  simp [Ref, withAccounts, RS.throw, Spec.pure, constErr] at h0 h8
  rw [h0] at h8
  cases h8

theorem rejects_constAbort (L : PoolLib) (D : DeployedIds) :
    ¬ RowSpec_233 L D constAbort := by
  intro h
  have h0 := h (withAccounts []) env0 trivial
  simp [Ref, withAccounts, RS.throw, Spec.pure, constAbort] at h0

end RSL.TX2_233
