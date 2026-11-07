/-
TX2:240  programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2
Frozen signature (r1_pool_adapter_owned.rs:463):
  pub(super) fn stage2(program_id: &Pubkey, accounts: &[AccountInfo<'_>], data: &[u8])
      -> ProgramResult
Route: guard-holding wrapper (snapshot holds Ref guards): ReviewedTranscription
plus native cuts under (bj)/(bl); the owned child TX2:241 is havocked over its
full Result type in the harness and composed here by its RowSpec reference.
Children: CLOSED snapshot (TX2:239, here transcribed over the NLF_ RefCell
model: `RSL.snapshot`), OPEN TX2:241 (RowSpec_241 reference, SAME arguments:
the seven owned snapshots in order, data, and the Clock reply).  The ledger
inventory edge to FibreIndex::get (TX2:043) is a spurious resolution of
`Clock::get` (line 479), which is the sol_get_clock_sysvar syscall slot
(`Event.clock`, reply from `Env`, runtime row RuntimeClockSlotBinding).
`program::set_return_data(&[])` is the return-data syscall (RuntimeReturnData).
cu-profiling is off: no log lines.
State: the SDK parent state (cells with borrow tokens, token counter).  The
post-state is the state after the seven snapshot acquire/release pairs; stage2
writes no account data.  On the early Err the state is unchanged and no event
occurs.
Own-input domain ((bf)(2)), recorded as caller clause of TX2:221:
  (D2') for seven accounts, if accounts[6]'s data payload has 1768 bytes and
        accounts[0]'s has 58295 bytes, Root0(payload6, payload0[688..58295])
        holds in the entry state.  It is exactly TX2:241's (D2) at the snapshot
        values; (D1) holds by the snapshot law and needs no clause.
-/
import RSL_TX2_241
set_option autoImplicit false

namespace RSL.TX2_240
open TX2_241 (V2Lib)

structure Args where
  program_id : B32
  accounts : List AccountInfo
  data : Bytes

/-- (length1, length2) of the seven snapshot calls, lines 471-477. -/
def snapLens : List (Nat × Nat) :=
  [(PROOF_ACCOUNT_BYTES, PROOF_ACCOUNT_BYTES), (MASTER_ACCOUNT_BYTES, MASTER_ACCOUNT_BYTES),
   (CHECKPOINT_ACCOUNT_BYTES, CHECKPOINT_ACCOUNT_BYTES), (LANE_ACCOUNT_BYTES, LANE_ACCOUNT_BYTES),
   (REGISTRY_BYTES, REGISTRY_V2_BYTES), (ENTRY_BYTES, ENTRY_V2_BYTES),
   (CHECKPOINT_BYTES, CHECKPOINT_BYTES)]

/-- The array literal of snapshots, evaluated in index order. -/
def snapAll : List AccountInfo → List (Nat × Nat) → SdkState → Spec (List OwnedAccount × SdkState)
  | a :: as, (l1, l2) :: ls, s =>
      Spec.bind (snapshot a l1 l2 s) fun r =>
      Spec.bind (snapAll as ls r.2) fun r2 =>
      Spec.pure (r.1 :: r2.1, r2.2)
  | _, _, s => Spec.pure ([], s)

def badRoute (a : Args) : Bool :=
  a.accounts.length != 7 || decide (a.data.length < 4) || a.data.take 4 != REQUEST_MAGIC

/-- Reference over the SDK parent state. -/
def Ref (L : PoolLib) (D : DeployedIds) (V : V2Lib) (a : Args) (s : SdkState) :
    Spec (Except ProgramError Unit × SdkState) :=
  if badRoute a then Spec.pure (.error .invalidInstructionData, s) else
  Spec.bind (Spec.emit (.returnData [])) fun _ =>
  Spec.bind (snapAll a.accounts snapLens s) fun r =>
  Spec.bind (Spec.env Env.clock) fun c =>
  Spec.bind (Spec.emit (.clock c)) fun _ =>
  Spec.bind (Spec.call (TX2_241.Domain V) (TX2_241.Ref L D V) ⟨a.program_id, r.1, a.data, c⟩)
    fun res => Spec.pure (res, r.2)

/-- Own-input domain (D2'). -/
def Domain (V : V2Lib) (a : Args) (s : SdkState) : Prop :=
  ∀ a0 a6, a.accounts.length = 7 → a.accounts[0]? = some a0 → a.accounts[6]? = some a6 →
    (payload a6 s).length = CHECKPOINT_BYTES → (payload a0 s).length = PROOF_ACCOUNT_BYTES →
    V.Root0 (payload a6 s) (slice (payload a0 s) AFTERSTATE_BYTES PROOF_ACCOUNT_BYTES)

def RowSpec_240 (L : PoolLib) (D : DeployedIds) (V : V2Lib)
    (stage2 : Args → SdkState → Env → Obs (Except ProgramError Unit × SdkState)) : Prop :=
  ∀ a s env, Domain V a s → Ref L D V a s env (stage2 a s env)

/-! ## Rejection of trivial implementations

A silent implementation (no events) returning any constant Err with any
post-state is rejected: on an admitted ASQ8 route the first event must be the
`set_return_data(&[])` syscall.  A constant abort is rejected on the empty
account list, which must return exactly (Err(InvalidInstructionData), s). -/

def silentErr (e : ProgramError) (f : SdkState → SdkState) :
    Args → SdkState → Env → Obs (Except ProgramError Unit × SdkState) :=
  fun _ s _ => ⟨.ret (.error e, f s), []⟩

def acc0 : AccountInfo := ⟨zero32, zero32, false, false, false, 0⟩
def st0 : SdkState := ⟨fun _ => ⟨[], [], none⟩, 0⟩

theorem rejects_silentErr (L : PoolLib) (D : DeployedIds) (V : V2Lib) (e : ProgramError)
    (f : SdkState → SdkState) : ¬ RowSpec_240 L D V (silentErr e f) := by
  intro h
  have h1 := h ⟨zero32, List.replicate 7 acc0, REQUEST_MAGIC⟩ st0 env0 (by
    intro a0 a6 _ _ h6 _ hl
    simp [payload, st0, PROOF_ACCOUNT_BYTES, AFTERSTATE_BYTES, PROOF_BYTES] at hl)
  unfold Ref at h1
  have hb : badRoute ⟨zero32, List.replicate 7 acc0, REQUEST_MAGIC⟩ = false := by decide
  rw [hb] at h1
  simp only [Bool.false_eq_true, if_false] at h1
  obtain ⟨rest, hr⟩ := Spec.bind_emit_head _ _ _ _ h1
  simp [silentErr] at hr

theorem rejects_constAbort (L : PoolLib) (D : DeployedIds) (V : V2Lib) :
    ¬ RowSpec_240 L D V (fun a s => constAbort (a, s)) := by
  intro h
  have h1 := h ⟨zero32, [], []⟩ st0 env0 (by intro _ _ h7; simp at h7)
  unfold Ref at h1
  have hb : badRoute ⟨zero32, [], []⟩ = true := by decide
  rw [hb] at h1
  simp [Spec.pure, constAbort] at h1

end RSL.TX2_240
