/-
TX2:234  programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::authenticate_invariant_release_registry
Frozen signature (r1_pool_adapter_owned.rs:81):
  fn authenticate_invariant_release_registry(
      verifier_program: &Pubkey, pool_program: &Pubkey,
      master_account: &OwnedAccount, master: &PoolV1PairForestMasterV1,
      registry_account: &OwnedAccount, entry_account: &OwnedAccount,
      current_slot: u64) -> ProgramResult
(The owned module's definition shadows the AccountInfo version at
r1_pool_adapter.rs:523; this row is the owned one, called from TX2:233.)
Route: emitted body under (bm).
Children (all CLOSED): pool_program_id / registry_program_id (TX2:220/225),
validate_verifier_policy_v1 (TX2:151), require_readonly_account (TX2:236),
OwnedAccount::data/key (TX2:229/231), decode_verifier_registry_v1/v2 and
entry_v1/v2 (TX2:203/204/201/202), is_immutable/is_paused (TX2:197-200),
is_active_at (TX2:194/196); create_program_address is the PDA syscall slot
(ruling (at)), an `Event.pda` with its quantified reply.
Own-input domain ((bf)(2)): none.
Effects: the ordered PDA syscall events only; no account or return-data write.
-/
import RSL_Pool
set_option autoImplicit false

namespace RSL.TX2_234

structure Args where
  verifier_program : B32
  pool_program : B32
  master_account : OwnedAccount
  master : Master
  registry_account : OwnedAccount
  entry_account : OwnedAccount
  current_slot : UInt64

/-- Lines 93-100. -/
def policyBad (D : DeployedIds) (a : Args) : Bool :=
  let p := a.master.verifier_policy
  decide (a.pool_program ≠ D.pool)
  || p.flags &&& POLICY_FLAG_IMMUTABLE_REGISTRY == 0
  || decide (p.registry_program ≠ D.registry)
  || decide (p.registry_authority ≠ zero32)
  || decide (p.policy_binding ≠ AUDIT_POLICY_BINDING)

def mk1 (x : UInt8) : Bytes := [x]

/-- Lines 128-136. -/
def registryV2Bad (D : DeployedIds) (a : Args) (r : RegistryV2) (rpd : B32) : Bool :=
  let p := a.master.verifier_policy
  decide (r.pool ≠ a.master_account.key) || decide (r.authority ≠ p.registry_authority)
  || decide (r.policy_binding ≠ p.policy_binding) || decide (r.registry_program ≠ D.registry)
  || decide (r.loader_program ≠ LOADER_ID) || decide (r.programdata_address ≠ rpd)
  || !r.is_immutable || r.is_paused

/-- Lines 161-171. -/
def entryV2Bad (a : Args) (e : EntryV2) (vpd : B32) : Bool :=
  decide (e.pool ≠ a.master_account.key) || decide (e.policy_binding ≠ AUDIT_POLICY_BINDING)
  || decide (e.verifier_program ≠ a.verifier_program)
  || decide (e.profile_binding ≠ PROFILE_BINDING) || decide (e.release_binding ≠ RELEASE_BINDING)
  || e.statement_version != TERMINAL_VERSION || decide (e.loader_program ≠ LOADER_ID)
  || decide (e.programdata_address ≠ vpd) || decide (e.expected_upgrade_authority ≠ zero32)
  || !e.is_active_at a.current_slot

/-- Lines 191-197. -/
def registryV1Bad (a : Args) (r : RegistryV1) : Bool :=
  let p := a.master.verifier_policy
  decide (r.pool ≠ a.master_account.key) || decide (r.authority ≠ p.registry_authority)
  || decide (r.policy_binding ≠ p.policy_binding) || !r.is_immutable || r.is_paused

/-- Lines 216-223. -/
def entryV1Bad (a : Args) (e : EntryV1) : Bool :=
  decide (e.pool ≠ a.master_account.key) || decide (e.policy_binding ≠ AUDIT_POLICY_BINDING)
  || decide (e.verifier_program ≠ a.verifier_program)
  || decide (e.profile_binding ≠ PROFILE_BINDING) || decide (e.release_binding ≠ RELEASE_BINDING)
  || e.statement_version != TERMINAL_VERSION || !e.is_active_at a.current_slot

/-- Immutable-deployment branch, lines 107-175, in source order. -/
def immutableBranch (L : PoolLib) (D : DeployedIds) (a : Args) : RS Unit :=
  let reg := D.registry
  let mk := a.master_account.key.bytes
  RS.bind (RS.ofExcept a.registry_account.data) fun rdata =>
  RS.bind (RS.ofOption (L.decodeRegistryV2 rdata) .invalidAccountData) fun r =>
  RS.bind (pdaOrErr [SEED_REGISTRY_V2, mk, mk1 r.bump] reg) fun expected =>
  RS.seq (RS.check (decide (a.registry_account.key ≠ expected)) .invalidAccountData) <|
  RS.bind (pdaOrErr [reg.bytes, mk1 r.programdata_bump] LOADER_ID) fun rpd =>
  RS.seq (RS.check (registryV2Bad D a r rpd) .invalidAccountData) <|
  RS.seq (RS.ofExcept (readonlyAccount a.entry_account reg)) <|
  RS.bind (RS.ofExcept a.entry_account.data) fun edata =>
  RS.bind (RS.ofOption (L.decodeEntryV2 edata) .invalidAccountData) fun e =>
  RS.bind (pdaOrErr [SEED_ENTRY_V2, mk, PROFILE_BINDING.bytes, RELEASE_BINDING.bytes, mk1 e.bump]
      reg) fun expectedE =>
  RS.seq (RS.check (decide (a.entry_account.key ≠ expectedE)) .invalidAccountData) <|
  RS.bind (pdaOrErr [a.verifier_program.bytes, mk1 e.programdata_bump] LOADER_ID) fun vpd =>
  RS.seq (RS.check (entryV2Bad a e vpd) .invalidAccountData) <|
  RS.pure ()

/-- V1 branch, lines 177-226, in source order. -/
def v1Branch (L : PoolLib) (D : DeployedIds) (a : Args) : RS Unit :=
  let reg := D.registry
  let mk := a.master_account.key.bytes
  RS.bind (RS.ofExcept a.registry_account.data) fun rdata =>
  RS.bind (RS.ofOption (L.decodeRegistryV1 rdata) .invalidAccountData) fun r =>
  RS.bind (pdaOrErr [SEED_REGISTRY, mk, mk1 r.bump] reg) fun expected =>
  RS.seq (RS.check (decide (a.registry_account.key ≠ expected)) .invalidAccountData) <|
  RS.seq (RS.check (registryV1Bad a r) .invalidAccountData) <|
  RS.seq (RS.ofExcept (readonlyAccount a.entry_account reg)) <|
  RS.bind (RS.ofExcept a.entry_account.data) fun edata =>
  RS.bind (RS.ofOption (L.decodeEntryV1 edata) .invalidAccountData) fun e =>
  RS.bind (pdaOrErr [SEED_ENTRY, mk, PROFILE_BINDING.bytes, RELEASE_BINDING.bytes, mk1 e.bump]
      reg) fun expectedE =>
  RS.seq (RS.check (decide (a.entry_account.key ≠ expectedE)) .invalidAccountData) <|
  RS.seq (RS.check (entryV1Bad a e) .invalidAccountData) <|
  RS.pure ()

/-- Reference: the complete body. -/
def Ref (L : PoolLib) (D : DeployedIds) (a : Args) : RS Unit :=
  RS.seq (RS.check (policyBad D a) .invalidAccountData) <|
  RS.seq (RS.check (!L.validatePolicy a.master.verifier_policy) .invalidAccountData) <|
  RS.seq (RS.ofExcept (readonlyAccount a.registry_account D.registry)) <|
  if a.master.verifier_policy.flags &&& POLICY_FLAG_IMMUTABLE_DEPLOYMENT != 0 then
    immutableBranch L D a
  else
    v1Branch L D a

/-- Own-input domain: none. -/
def Domain (_a : Args) : Prop := True

/-- RowSpec_234.  `L`, `D` are instantiated only with the CLOSED models named
in RSL_Pool (gate-checked). -/
def RowSpec_234 (L : PoolLib) (D : DeployedIds)
    (authenticate_invariant_release_registry : Args → Env → Obs (Except ProgramError Unit)) :
    Prop :=
  ∀ a env, Domain a → Ref L D a env (authenticate_invariant_release_registry a env)

/-! ## Rejection of trivial implementations

Two inputs that reach different first errors before any CLOSED decoder runs:
(i) a signer registry account fails `require_readonly_account` with
InvalidAccountData; (ii) a read-only registry account whose snapshot carries
AccountBorrowFailed propagates that error through `data()?`.  Both need only a
policy that the CLOSED validator accepts. -/

def acct (signer : Bool) (owner : B32) (bytes : Except ProgramError Bytes) : OwnedAccount :=
  ⟨zero32, owner, signer, false, false, .ok 0, bytes⟩

def goodPolicy (D : DeployedIds) : VerifierPolicy :=
  ⟨POLICY_FLAG_IMMUTABLE_REGISTRY, D.registry, zero32, AUDIT_POLICY_BINDING⟩

def master0 (D : DeployedIds) : Master :=
  ⟨0, ⟨zero32, zero32, zero32, 0, zero32⟩, goodPolicy D, 0, false, 0, []⟩

def input (D : DeployedIds) (reg : OwnedAccount) : Args :=
  ⟨zero32, D.pool, acct false zero32 (.ok []), master0 D, reg, acct false zero32 (.ok []), 0⟩

theorem policy_ok (D : DeployedIds) (reg : OwnedAccount) : policyBad D (input D reg) = false := by
  simp [policyBad, input, master0, goodPolicy, POLICY_FLAG_IMMUTABLE_REGISTRY]

theorem rejects_constErr (L : PoolLib) (D : DeployedIds)
    (hp : L.validatePolicy (goodPolicy D) = true) (e : ProgramError) :
    ¬ RowSpec_234 L D (constErr e) := by
  intro h
  have h1 := h (input D (acct true D.registry (.ok []))) env0 trivial
  have h2 := h (input D (acct false D.registry (.error .accountBorrowFailed))) env0 trivial
  have hp' : L.validatePolicy (input D (acct true D.registry (.ok []))).master.verifier_policy = true := hp
  have hp'' : L.validatePolicy
      (input D (acct false D.registry (.error .accountBorrowFailed))).master.verifier_policy = true := hp
  unfold Ref at h1 h2
  rw [policy_ok, RS.check_false, RS.seq_pure, hp', Bool.not_true, RS.check_false, RS.seq_pure] at h1
  rw [policy_ok, RS.check_false, RS.seq_pure, hp'', Bool.not_true, RS.check_false, RS.seq_pure] at h2
  have r1 : readonlyAccount (input D (acct true D.registry (.ok []))).registry_account D.registry
      = .error .invalidAccountData := by simp [readonlyAccount, input, acct]
  have r2 : readonlyAccount (input D (acct false D.registry (.error .accountBorrowFailed))).registry_account
      D.registry = .ok () := by simp [readonlyAccount, input, acct]
  rw [r1, RS.ofExcept_error, RS.seq_throw] at h1
  rw [r2, RS.ofExcept_ok, RS.seq_pure] at h2
  have hflag : ((input D (acct false D.registry (.error .accountBorrowFailed))).master.verifier_policy.flags
      &&& POLICY_FLAG_IMMUTABLE_DEPLOYMENT != 0) = false := by
    show ((POLICY_FLAG_IMMUTABLE_REGISTRY &&& POLICY_FLAG_IMMUTABLE_DEPLOYMENT) != 0) = false
    decide
  rw [hflag] at h2
  simp only [Bool.false_eq_true, if_false] at h2
  unfold v1Branch at h2
  simp only [input, acct, OwnedAccount.data] at h2
  rw [RS.ofExcept_error, RS.bind_throw] at h2
  simp [RS.throw, Spec.pure, constErr] at h1 h2
  rw [h1] at h2
  cases h2

theorem rejects_constAbort (L : PoolLib) (D : DeployedIds)
    (hp : L.validatePolicy (goodPolicy D) = true) :
    ¬ RowSpec_234 L D constAbort := by
  intro h
  have h1 := h (input D (acct true D.registry (.ok []))) env0 trivial
  have hp' : L.validatePolicy (input D (acct true D.registry (.ok []))).master.verifier_policy = true := hp
  unfold Ref at h1
  rw [policy_ok, RS.check_false, RS.seq_pure, hp', Bool.not_true, RS.check_false, RS.seq_pure] at h1
  have r1 : readonlyAccount (input D (acct true D.registry (.ok []))).registry_account D.registry
      = .error .invalidAccountData := by simp [readonlyAccount, input, acct]
  rw [r1, RS.ofExcept_error, RS.seq_throw] at h1
  simp [RS.throw, Spec.pure, constAbort] at h1

end RSL.TX2_234
