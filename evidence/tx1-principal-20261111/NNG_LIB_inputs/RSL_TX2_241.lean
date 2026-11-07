/-
TX2:241  programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2_owned
Frozen signature (r1_pool_adapter_owned.rs:417):
  fn stage2_owned(program_id: &Pubkey, accounts: &[OwnedAccount], data: &[u8],
      current_slot: Result<u64, ProgramError>) -> ProgramResult
Route: emitted body under (bm).
Children: OPEN TX2:242 (RowSpec_242 reference); TX2:064 tx2_authenticated
(CANDIDATE NMN_064.root; enters through `V2Lib.tx2auth` with its own domain
`Dom064`, discharged here at SAME arguments); CLOSED OwnedAccount::data
(TX2:229), encode_pool_v1_pair_forest_terminal_statement_v1 (TX2:165),
lib.rs::error (TX2:211: one `msg!("r1:error:{:?}", e)` log line then
InvalidInstructionData), lib.rs::observer (TX2:212: None in the release
build; the obs argument is fixed to None, ruling (al)), SolanaDigest (the
deployed H, ruling (al)), emit_result (TX2:219).
Own-input domain ((bf)(2)), recorded as caller clauses of TX2:240:
  (D1) every OwnedAccount is snapshot-consistent: bytes = Ok d -> length = Ok |d|;
  (D2) Root0 provenance at the SAME inputs: for 7 accounts whose proof image
       (accounts[0]) has the admitted 58295 bytes, Root0(accounts[6] bytes,
       accounts[0] bytes[688..58295]).  This is TX2:064's own Root0 clause
       transported to this row's arguments; NMN_064 records its installation as
       OPEN at 241.  It propagates to TX2:240/221/213 and is discharged at the
       entry only by the headline hypotheses (RuntimePersistence data-only plus
       NMF_GameRoot "Root0 or existing charged collision"), see RSL_INDEX.md.
Effects, in order: TX2:242's events; the encoder (CLOSED law; the frozen
encoder returns an array); TX2:064's
ordered digest/oracle chronology (its abort arm carries only its prefix);
on a TX2:064 Err one log line; then emit_result's return-data event.
Revision 2 (RSL_REVISION2.md): the two `data()?` clones are allocation sites for
a heap-carrying deferred error (`RS.ofCloned`, NMT-S1 shape), and the `error`
path has its `format!` allocation before the log line.  At the only caller,
TX2:240, every snapshot satisfies `OwnedAccount.SnapshotErrs`
(RSL_TX1_344.snapAll_errs), so the clone arms are unreachable there.
-/
import RSL_TX2_242
set_option autoImplicit false

namespace RSL.TX2_241

/-- Verifier-side interface for TX2 (CANDIDATE/CLOSED verifier rows). -/
structure V2Lib where
  /-- `verifier::Error`. -/
  VErr : Type
  /-- `format!("{:?}", e)`, the payload of lib.rs::error's log line (CLOSED TX2:211). -/
  debug : VErr → String
  /-- NLP_InputDomain.Root0 (checkpoint, proof) on byte carriers. -/
  Root0 : Bytes → Bytes → Prop
  /-- TX2:064 `tx2_authenticated(public, proof, checkpoint, SolanaDigest, None)`:
  its complete law (NMN_064.RowSpec: Law + chronology, abort = prefix only).
  Revision 3 (ruling (bq), LIB0_ F1): the heap::filled reservations reached
  through `resume` (verifier.rs:428) read `Env.reservation`
  (`Spec.tryReserve`), so on `Dom064` the law is a function of the arguments
  and Env (`Spec.Functional (tx2auth x.1 x.2.1 x.2.2)`, required at the gate). -/
  tx2auth : Bytes → Bytes → Bytes → Spec (Except VErr Unit)

/-- TX2:064's own-input domain (NMN_064.Domain). -/
def Dom064 (V : V2Lib) (x : Bytes × Bytes × Bytes) : Prop :=
  x.2.1.length = PROOF_BYTES ∧ x.2.2.length = CHECKPOINT_BYTES ∧ x.1.length ≤ STATEMENT_BYTES
  ∧ V.Root0 x.2.2 x.2.1

/-- `.map_err(super::super::error)?` (lib.rs:40): the `format!` String
allocation of `msg!("r1:error:{:?}", e)` (Revision 2; abort = prefix so far),
one log line, then InvalidInstructionData. -/
def mapVErr (V : V2Lib) (r : Except V.VErr Unit) : RS Unit :=
  match r with
  | .ok () => RS.pure ()
  | .error e => RS.seq (RS.lift Spec.alloc) <|   -- format! builds the message String
               RS.seq (RS.lift (Spec.emit (.log ("r1:error:" ++ V.debug e))))
                  (RS.throw .invalidInstructionData)

structure Args where
  program_id : B32
  accounts : List OwnedAccount
  data : Bytes
  current_slot : Except ProgramError UInt64

/-- usize::checked_add on the 64-bit SBF target. -/
def USIZE_LIMIT : Nat := 18446744073709551616

def Ref (L : PoolLib) (D : DeployedIds) (V : V2Lib) (a : Args) : RS Unit :=
  RS.seq (RS.check (a.accounts.length != 7 || decide (a.data.length < 4)
                    || a.data.take 4 != REQUEST_MAGIC) .invalidInstructionData) <|
  RS.bind (Spec.call TX2_242.Domain (TX2_242.Ref L D)
            ⟨a.program_id, a.accounts, a.data, a.current_slot⟩) fun validated =>
  RS.bind (RS.index a.accounts 0) fun acc0 =>
  RS.bind acc0.data fun proofData =>
  RS.bind (RS.index a.accounts 6) fun acc6 =>
  RS.bind acc6.data fun checkpointData =>
  RS.seq (RS.check (decide (USIZE_LIMIT ≤ AFTERSTATE_BYTES + validated.proof_length))
            .invalidAccountData) <|
  let proofEnd := AFTERSTATE_BYTES + validated.proof_length
  RS.seq (RS.check (proofData.length != proofEnd) .invalidAccountData) <|
  RS.bind (RS.lift (L.encodeStatement validated.statement)) fun enc =>
  RS.bind (RS.ofOption enc .invalidInstructionData) fun publicBytes =>
  RS.seq (RS.check (publicBytes.length != STATEMENT_BYTES) .invalidInstructionData) <|
  RS.bind (RS.lift (Spec.call (Dom064 V) (fun x => V.tx2auth x.1 x.2.1 x.2.2)
            (publicBytes, slice proofData AFTERSTATE_BYTES proofEnd, checkpointData))) fun r =>
  RS.seq (mapVErr V r) <|
  L.emitResult validated.statement

/-- (D1) snapshot consistency. -/
def Consistent (x : OwnedAccount) : Prop := ∀ d, x.bytes = .ok d → x.length = .ok d.length

/-- Own-input domain: (D1) and (D2). -/
def Domain (V : V2Lib) (a : Args) : Prop :=
  (∀ x ∈ a.accounts, Consistent x) ∧
  (∀ acc0 acc6 ck pr, a.accounts.length = 7 → a.accounts[0]? = some acc0 →
     a.accounts[6]? = some acc6 → acc6.bytes = .ok ck → acc0.bytes = .ok pr →
     pr.length = PROOF_ACCOUNT_BYTES → V.Root0 ck (slice pr AFTERSTATE_BYTES PROOF_ACCOUNT_BYTES))

def RowSpec_241 (L : PoolLib) (D : DeployedIds) (V : V2Lib)
    (stage2_owned : Args → Env → Obs (Except ProgramError Unit)) : Prop :=
  ∀ a env, Domain V a → Ref L D V a env (stage2_owned a env)

/-! ## Rejection of trivial implementations -/

def acct0 : OwnedAccount := ⟨zero32, zero32, false, false, false, .ok 0, .ok []⟩

theorem acct0_domain (V : V2Lib) (data : Bytes) (slot : Except ProgramError UInt64) :
    Domain V ⟨zero32, List.replicate 7 acct0, data, slot⟩ := by
  constructor
  · intro x hx d hd
    have hx' : x = acct0 := List.eq_of_mem_replicate hx
    subst hx'
    simp [acct0] at hd
    subst hd
    rfl
  · intro acc0 acc6 ck pr _ h0 _ _ hpr hlen
    have : acc0 = acct0 := by simpa using h0.symm
    subst this
    simp [acct0] at hpr
    subst hpr
    simp [PROOF_ACCOUNT_BYTES, AFTERSTATE_BYTES, PROOF_BYTES] at hlen

theorem rejects_constErr (L : PoolLib) (D : DeployedIds) (V : V2Lib)
    (d : Bytes) (q : L.Request) (lane : UInt8)
    (hlen : d.length = REQUEST_BYTES) (hmagic : d.take 4 = REQUEST_MAGIC)
    (hd : L.decodeRequest d = some q)
    (hb : (decide (L.reqProfile q ≠ PROFILE_BINDING) || decide (L.reqRelease q ≠ RELEASE_BINDING)
            || decide (L.reqPoolProgram q ≠ D.pool)) = false)
    (hl : L.outputLane (L.reqNullifier q) = some lane) (e : ProgramError) :
    ¬ RowSpec_241 L D V (constErr e) := by
  intro h
  have h1 := h ⟨zero32, [], d, .ok 0⟩ env0 ⟨by simp, by intro _ _ _ _ h7; simp at h7⟩
  have h2 := h ⟨zero32, List.replicate 7 acct0, d, .error .unsupportedSysvar⟩ env0
    (acct0_domain V d _)
  unfold Ref at h1 h2
  simp only at h1 h2
  have c1 : (([] : List OwnedAccount).length != 7 || decide (d.length < 4)
      || d.take 4 != REQUEST_MAGIC) = true := by simp
  rw [c1, RS.check_true, RS.seq_throw] at h1
  have c2 : ((List.replicate 7 acct0).length != 7 || decide (d.length < 4)
      || d.take 4 != REQUEST_MAGIC) = false := by
    simp [hmagic, hlen, REQUEST_BYTES]
  rw [c2, RS.check_false, RS.seq_pure, Spec.call_trivial _ _ _ trivial,
    TX2_242.ref_slot_error L D _ _ d q lane _ hlen hd hb hl, RS.bind_throw] at h2
  simp [RS.throw, Spec.pure, constErr] at h1 h2
  rw [h1] at h2
  cases h2

theorem rejects_constAbort (L : PoolLib) (D : DeployedIds) (V : V2Lib) :
    ¬ RowSpec_241 L D V constAbort := by
  intro h
  have h1 := h ⟨zero32, [], [], .ok 0⟩ env0 ⟨by simp, by intro _ _ _ _ h7; simp at h7⟩
  unfold Ref at h1
  simp only at h1
  have c1 : (([] : List OwnedAccount).length != 7 || decide (([] : Bytes).length < 4)
      || ([] : Bytes).take 4 != REQUEST_MAGIC) = true := by decide
  rw [c1, RS.check_true, RS.seq_throw] at h1
  simp [RS.throw, Spec.pure, constAbort] at h1

end RSL.TX2_241
