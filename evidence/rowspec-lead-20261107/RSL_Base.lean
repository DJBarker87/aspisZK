/-
RSL_Base: shared carriers and the relational reference monad for the canonical
RowSpec package (RSL_).  Core Lean only (no Mathlib, no Aeneas) so that every
spec module is checkable on a development machine.

Frozen source: 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387, program features
{pool-adapter, private-leaf-salts}, no cu-profiling, no prover, no detail-phases.

Semantics of a RowSpec.  For a row with argument tuple `A` and Rust return type
`T`, the worker supplies the observed semantics of the ACTUAL frozen function,
`impl : A -> Env -> Obs T` (for an emitted body: the Aeneas body with each
child call interpreted by that child's CLOSED root / RowSpec, ok/fail/div mapped
to `Exit.ret/abort/diverge`; for a guard-holding wrapper: the ReviewedTranscription
evaluated on the parent state, joined to the native cut relation under (bj)/(bl)).
The RowSpec states that, on the row's own-input domain, the observation lies in
the reference relation `Ref : A -> Spec T`, a line-by-line transcription of the
frozen body in which
  * every Rust `Ok`/`Err` value is exact (ProgramError is the complete 2.2.2
    carrier, payloads included);
  * every observable effect (syscall/oracle query with its reply, log line,
    return-data write, account-data write, RefCell token acquire/release) is an
    `Event`, in source order;
  * a panic, a stopped child, or an allocation failure is `Exit.abort` carrying
    ONLY the event prefix up to that point (ruling (bl)(3)); no post-abort
    state is stated or invented;
  * the only nondeterminism is the allocation-failure branch at each named
    allocation site (ruling (bl)(3): allocator internals are outside every
    obligation, a failure aborts).  There is no generic "may abort anywhere"
    clause, so a constant-abort or constant-Err implementation is rejected
    (each row module carries the rejection examples).
Oracle replies (sha256, create_program_address, Clock) come from `Env`, which
the RowSpec quantifies universally; binding them to the runtime is the job of
the accepted runtime rows (ruling (at): the PDA reply is the quantified slot).
-/
set_option autoImplicit false

namespace RSL

/-! ## Byte carriers -/

abbrev Bytes := List UInt8

/-- `[u8; 32]` / `Pubkey`: exactly 32 bytes. -/
structure B32 where
  bytes : List UInt8
  len : bytes.length = 32

instance : DecidableEq B32 := fun a b =>
  if h : a.bytes = b.bytes then
    isTrue (by cases a; cases b; cases h; rfl)
  else
    isFalse (by intro e; apply h; rw [e])

def B32.ofFill (v : UInt8) : B32 := ⟨List.replicate 32 v, by simp⟩

/-- `[0u8; 32]`. -/
def zero32 : B32 := B32.ofFill 0

/-- `Digest = [M31; 8]`, limbs as `u32` values. -/
abbrev Digest := List UInt32

/-- Little-endian `u32` from four bytes. -/
def le32 (b0 b1 b2 b3 : UInt8) : UInt32 :=
  b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)

/-- Little-endian `u64` from the first eight bytes (callers check the length). -/
def le64 (b : Bytes) : UInt64 :=
  (b.take 8).foldr (fun x acc => (acc <<< 8) ||| x.toUInt64) 0

/-- `u64::to_le_bytes`. -/
def u64le (x : UInt64) : Bytes :=
  (List.range 8).map (fun i => (x >>> (8 * i).toUInt64).toUInt8)

/-- Field modulus of M31. -/
def P31 : UInt32 := 0x7fffffff

/-- Byte slice `b[i..j]`. -/
def slice (b : Bytes) (i j : Nat) : Bytes := (b.drop i).take (j - i)

/-! ## ProgramError: complete solana-program-error 2.2.2 carrier -/

inductive ProgramError where
  | custom (code : UInt32)
  | invalidArgument
  | invalidInstructionData
  | invalidAccountData
  | accountDataTooSmall
  | insufficientFunds
  | incorrectProgramId
  | missingRequiredSignature
  | accountAlreadyInitialized
  | uninitializedAccount
  | notEnoughAccountKeys
  | accountBorrowFailed
  | maxSeedLengthExceeded
  | invalidSeeds
  | borshIoError (msg : String)
  | accountNotRentExempt
  | unsupportedSysvar
  | illegalOwner
  | maxAccountsDataAllocationsExceeded
  | invalidRealloc
  | maxInstructionTraceLengthExceeded
  | builtinProgramsMustConsumeComputeUnits
  | invalidAccountOwner
  | arithmeticOverflow
  | immutable
  | incorrectAuthority
  deriving DecidableEq, Repr

/-! ## Events, oracle environment, observations -/

inductive Kind where
  | shared
  | exclusive
  deriving DecidableEq, Repr

inductive Event where
  /-- `sol_log_` line (msg!). -/
  | log (msg : String)
  /-- `sol_set_return_data` with these bytes. -/
  | returnData (bytes : Bytes)
  /-- `sol_sha256` (hashv, the deployed SolanaDigest) with its reply. -/
  | digest (parts : List Bytes) (out : B32)
  /-- `sol_create_program_address` with its reply (`none` = PubkeyError). -/
  | pda (seeds : List Bytes) (program : B32) (reply : Option B32)
  /-- `sol_get_clock_sysvar`, slot projection of the reply. -/
  | clock (reply : Except ProgramError UInt64)
  /-- RefCell borrow of the data cell `cell` with fresh token `token`;
  `ok := false` is the SDK `AccountBorrowFailed` reply (no token issued). -/
  | acquire (cell token : Nat) (kind : Kind) (ok : Bool)
  /-- Drop of a live guard (token consumed). -/
  | release (cell token : Nat) (kind : Kind)
  /-- Bytes written into account data cell `cell` through a live RefMut. -/
  | write (cell : Nat) (bytes : Bytes)

structure Env where
  sha256 : List Bytes → B32
  pda : List Bytes → B32 → Option B32
  clock : Except ProgramError UInt64

inductive Exit (α : Type) where
  | ret (a : α)
  | abort
  | diverge

structure Obs (α : Type) where
  exit : Exit α
  events : List Event

/-- Reference relation: which observations the frozen body admits. -/
def Spec (α : Type) : Type := Env → Obs α → Prop

namespace Spec

def pure {α : Type} (a : α) : Spec α := fun _ o => o = ⟨.ret a, []⟩

def bind {α β : Type} (m : Spec α) (k : α → Spec β) : Spec β := fun env o =>
  (∃ a e1 o2, m env ⟨.ret a, e1⟩ ∧ k a env o2 ∧ o = ⟨o2.exit, e1 ++ o2.events⟩) ∨
  (∃ e1, m env ⟨.abort, e1⟩ ∧ o = ⟨.abort, e1⟩) ∨
  (∃ e1, m env ⟨.diverge, e1⟩ ∧ o = ⟨.diverge, e1⟩)

instance : Monad Spec where
  pure := Spec.pure
  bind := Spec.bind

/-- One observable effect. -/
def emit (e : Event) : Spec Unit := fun _ o => o = ⟨.ret (), [e]⟩

/-- An allocation site (Box::new, Vec, to_vec, heap::filled ...).  Ruling
(bl)(3): either the fresh object exists, or the transaction aborts here with
the prefix so far. -/
def alloc : Spec Unit := fun _ o => o = ⟨.ret (), []⟩ ∨ o = ⟨.abort, []⟩

/-- A reachable Rust panic (index out of range, unwrap on None, ...). -/
def panic {α : Type} : Spec α := fun _ o => o = ⟨.abort, []⟩

/-- Read a value from the oracle environment, no event. -/
def env {α : Type} (f : Env → α) : Spec α := fun e o => o = ⟨.ret (f e), []⟩

/-- Call a child whose law is `law`, after its (bf)(2) own-argument domain
`dom` holds at the SAME argument.  If `dom` fails the reference admits no
observation, so the parent RowSpec is then unprovable: this is how the parent
spec carries the caller-clause discharge. -/
def call {A B : Type} (dom : A → Prop) (law : A → Spec B) (a : A) : Spec B :=
  fun e o => dom a ∧ law a e o

def map {α β : Type} (f : α → β) (m : Spec α) : Spec β :=
  bind m (fun a => pure (f a))

end Spec

/-! ## Rust `Result<_, ProgramError>` layer -/

/-- A Spec returning a Rust `Result<α, ProgramError>`. -/
def RS (α : Type) : Type := Spec (Except ProgramError α)

namespace RS

def pure {α : Type} (a : α) : RS α := Spec.pure (.ok a)
def throw {α : Type} (e : ProgramError) : RS α := Spec.pure (.error e)

def bind {α β : Type} (m : RS α) (k : α → RS β) : RS β :=
  Spec.bind m (fun r => match r with
    | .ok a => k a
    | .error e => Spec.pure (.error e))

instance : Monad RS where
  pure := RS.pure
  bind := RS.bind

/-- Lift an infallible Spec. -/
def lift {α : Type} (m : Spec α) : RS α := Spec.map Except.ok m

/-- `?` on a child Result whose error is mapped by `f` (map_err). -/
def tryMap {ε α : Type} (m : Spec (Except ε α)) (f : ε → ProgramError) : RS α :=
  Spec.map (fun r => match r with | .ok a => .ok a | .error e => .error (f e)) m

/-- `if bad { return Err(e) }`. -/
def check (bad : Bool) (e : ProgramError) : RS Unit :=
  if bad then throw e else pure ()

/-- `x.ok_or(e)?` / `.map_err(|_| e)?` on an Option-modelled CLOSED child. -/
def ofOption {α : Type} (x : Option α) (e : ProgramError) : RS α :=
  match x with | some a => pure a | none => throw e

def ofExcept {α : Type} (x : Except ProgramError α) : RS α := Spec.pure x

end RS

/-! ## Rewriting lemmas used by the rejection examples -/

theorem Spec.pure_iff {α : Type} (a : α) (env : Env) (o : Obs α) :
    Spec.pure a env o ↔ o = ⟨.ret a, []⟩ := Iff.rfl

theorem Spec.bind_pure {α β : Type} (a : α) (k : α → Spec β) :
    Spec.bind (Spec.pure a) k = k a := by
  funext env o
  apply propext
  constructor
  · intro h
    rcases h with ⟨a', e1, o2, hm, hk, ho⟩ | ⟨e1, hm, _⟩ | ⟨e1, hm, _⟩
    · simp only [Spec.pure, Obs.mk.injEq, Exit.ret.injEq] at hm
      rcases hm with ⟨rfl, rfl⟩
      subst ho
      cases o2
      simpa using hk
    · simp [Spec.pure] at hm
    · simp [Spec.pure] at hm
  · intro h
    exact Or.inl ⟨a, [], o, rfl, h, by cases o; rfl⟩

theorem RS.bind_throw {α β : Type} (e : ProgramError) (k : α → RS β) :
    RS.bind (RS.throw e) k = RS.throw e := by
  unfold RS.bind RS.throw
  rw [Spec.bind_pure]

theorem RS.bind_pure {α β : Type} (a : α) (k : α → RS β) :
    RS.bind (RS.pure a) k = k a := by
  unfold RS.bind RS.pure
  rw [Spec.bind_pure]

theorem RS.check_true {e : ProgramError} : RS.check true e = (RS.throw e : RS Unit) := rfl
theorem RS.check_false {e : ProgramError} : RS.check false e = (RS.pure () : RS Unit) := rfl


/-- `m?; k` for a unit-valued step. -/
def RS.seq {β : Type} (m : RS Unit) (k : RS β) : RS β := RS.bind m (fun _ => k)

theorem RS.seq_throw {β : Type} (e : ProgramError) (k : RS β) :
    RS.seq (RS.throw e) k = RS.throw e := RS.bind_throw e _

theorem RS.seq_pure {β : Type} (k : RS β) : RS.seq (RS.pure ()) k = k := RS.bind_pure () _

theorem RS.ofExcept_error {α : Type} (e : ProgramError) :
    (RS.ofExcept (.error e) : RS α) = RS.throw e := rfl
theorem RS.ofExcept_ok {α : Type} (a : α) : (RS.ofExcept (.ok a) : RS α) = RS.pure a := rfl
theorem RS.check_bool (b : Bool) (e : ProgramError) :
    RS.check b e = if b then RS.throw e else RS.pure () := rfl

/-- A `throw` reference admits exactly one observation. -/
theorem RS.throw_obs {α : Type} (e : ProgramError) (env : Env) (o : Obs (Except ProgramError α)) :
    (RS.throw e : RS α) env o ↔ o = ⟨.ret (.error e), []⟩ := Iff.rfl


/-- `alloc; Ok a` admits exactly the Ok observation or the allocation abort. -/
theorem RS.alloc_pure_obs {α : Type} (a : α) (env : Env) (o : Obs (Except ProgramError α))
    (h : RS.bind (RS.lift Spec.alloc) (fun _ => RS.pure a) env o) :
    o = ⟨.ret (.ok a), []⟩ ∨ o = ⟨.abort, []⟩ := by
  unfold RS.bind RS.lift Spec.map at h
  rcases h with ⟨r, e1, o2, hm, hk, ho⟩ | ⟨e1, hm, ho⟩ | ⟨e1, hm, ho⟩
  · rcases hm with ⟨u, e0, o0, ha, hp, hm⟩ | ⟨_, _, hm⟩ | ⟨_, _, hm⟩
    · rcases ha with ha | ha
      · simp only [Spec.pure, Obs.mk.injEq] at ha hp
        cases ha.2; subst hp
        simp only [Obs.mk.injEq, Exit.ret.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩
        simp only [RS.pure, Spec.pure] at hk
        subst hk; subst ho; exact Or.inl rfl
      · simp at ha
    · simp at hm
    · simp at hm
  · rcases hm with ⟨u, e0, o0, ha, hp, hm⟩ | ⟨e0, ha, hm⟩ | ⟨e0, ha, hm⟩
    · simp only [Spec.pure] at hp; subst hp; simp at hm
    · rcases ha with ha | ha
      · simp at ha
      · simp only [Obs.mk.injEq] at ha hm
        rcases hm with ⟨_, rfl⟩; rcases ha with ⟨_, rfl⟩
        subst ho; exact Or.inr rfl
    · rcases ha with ha | ha <;> simp_all
  · rcases hm with ⟨u, e0, o0, ha, hp, hm⟩ | ⟨e0, ha, hm⟩ | ⟨e0, ha, hm⟩
    · simp only [Spec.pure] at hp; subst hp; simp at hm
    · rcases ha with ha | ha <;> simp_all
    · rcases ha with ha | ha <;> simp_all

/-- Constant implementations used by every rejection example. -/
def constErr {A α : Type} (e : ProgramError) : A → Env → Obs (Except ProgramError α) :=
  fun _ _ => ⟨.ret (.error e), []⟩

def constAbort {A α : Type} : A → Env → Obs α := fun _ _ => ⟨.abort, []⟩

/-- A default oracle environment for examples (any Env works for the
pre-oracle checks the examples use). -/
def env0 : Env := ⟨fun _ => zero32, fun _ _ => none, .error .unsupportedSysvar⟩

/-! ## Owned account snapshot (r1_pool_adapter_owned.rs:9-25) -/

structure OwnedAccount where
  key : B32
  owner : B32
  is_signer : Bool
  is_writable : Bool
  executable : Bool
  length : Except ProgramError Nat
  bytes : Except ProgramError Bytes

/-- `OwnedAccount::data` (CLOSED TX1:335 / TX2:229, NHJ_DataPacket): Ok(&bytes)
or Err(error.clone()); no effect. -/
def OwnedAccount.data (a : OwnedAccount) : Except ProgramError Bytes := a.bytes
/-- `OwnedAccount::data_len`. -/
def OwnedAccount.data_len (a : OwnedAccount) : Except ProgramError Nat := a.length

/-! ## CLOSED pure helpers, transcribed (each worker proves the CLOSED root
implies the transcription on the call domain, (bm)(2)(c)). -/

/-- `readonly_buffer_meta_ok` / `require_readonly_buffer` (CLOSED TX1:340, TX2:237). -/
def readonlyBuffer (a : OwnedAccount) : Except ProgramError Unit :=
  if a.is_signer || a.is_writable || a.executable then .error .invalidAccountData else .ok ()

/-- `readonly_meta_ok` / `require_readonly_account` (CLOSED TX2:236). -/
def readonlyAccount (a : OwnedAccount) (owner : B32) : Except ProgramError Unit :=
  if decide (a.owner ≠ owner) || a.is_signer || a.is_writable || a.executable then
    .error .invalidAccountData else .ok ()

/-- `verifier::checkpoint_size(Variant::S2)` = CHECKPOINT_FIXED + 16*64 = 1768. -/
def CHECKPOINT_BYTES : Nat := 1768

/-- `require_verifier_checkpoint` (CLOSED TX1:341, TX2:238), with the exact
short-circuit: `data_len()?` is evaluated only if the four metadata tests pass,
and its Err is returned unchanged. -/
def verifierCheckpoint (a : OwnedAccount) (program : B32) (writable : Bool) :
    Except ProgramError Unit :=
  if decide (a.owner ≠ program) || a.is_signer || a.executable || a.is_writable != writable then
    .error .invalidAccountData
  else match a.data_len with
    | .error e => .error e
    | .ok n => if n != CHECKPOINT_BYTES then .error .invalidAccountData else .ok ()

/-- Pairwise distinct keys (the Result of `require_distinct_accounts`, CLOSED
TX1:339 / TX2:235; the scan order does not affect the Result, whose only
error is InvalidArgument, and the helper has no effect). -/
def distinctKeys : List OwnedAccount → Bool
  | [] => true
  | a :: rest => rest.all (fun b => decide (b.key ≠ a.key)) && distinctKeys rest

def requireDistinct (as : List OwnedAccount) : Except ProgramError Unit :=
  if distinctKeys as then .ok () else .error .invalidArgument

/-- `require_zero` (CLOSED TX1:342). -/
def requireZero (b : Bytes) : Except ProgramError Unit :=
  if b.all (· == 0) then .ok () else .error .accountAlreadyInitialized

/-! ## SDK AccountInfo / RefCell model (transcribes NLF_RefCell, NLF_SdkModel
and NLF_ParentModel: same admission rules, Err on conflict, payload identity,
release on drop, globally fresh tokens).  Account identity with cells comes from
RuntimeEntrypointAdmission (duplicate keys share a cell). -/

structure Cell where
  payload : Bytes
  readers : List Nat
  writer : Option Nat

/-- Immutable AccountInfo descriptor fields plus the index of its data cell. -/
structure AccountInfo where
  key : B32
  owner : B32
  is_signer : Bool
  is_writable : Bool
  executable : Bool
  cell : Nat

structure SdkState where
  cells : Nat → Cell
  next : Nat

def SdkState.put (s : SdkState) (i : Nat) (c : Cell) : SdkState :=
  { s with cells := fun j => if j = i then c else s.cells j }

def sharedOk (c : Cell) : Bool :=
  c.writer.isNone && decide (c.readers.length < 9223372036854775807)
def exclusiveOk (c : Cell) : Bool := c.writer.isNone && c.readers.isEmpty

/-- `try_borrow_data` / `try_borrow_mut_data`: one acquire event with fresh
token `s.next`; on conflict Err(AccountBorrowFailed) and the cell is unchanged.
The token counter advances in both cases (NLF_ParentModel.acquire). -/
def acquire (a : AccountInfo) (k : Kind) (s : SdkState) :
    Spec (Except ProgramError Nat × SdkState) :=
  let c := s.cells a.cell
  let t := s.next
  let ok := match k with | .shared => sharedOk c | .exclusive => exclusiveOk c
  if ok then
    let c' : Cell := match k with
      | .shared => { c with readers := t :: c.readers }
      | .exclusive => { c with writer := some t }
    Spec.bind (Spec.emit (.acquire a.cell t k true))
      (fun _ => Spec.pure (.ok t, { (s.put a.cell c') with next := t + 1 }))
  else
    Spec.bind (Spec.emit (.acquire a.cell t k false))
      (fun _ => Spec.pure (.error .accountBorrowFailed, { s with next := t + 1 }))

/-- Guard drop: consumes the token. -/
def release (a : AccountInfo) (t : Nat) (k : Kind) (s : SdkState) : Spec SdkState :=
  let c := s.cells a.cell
  let c' : Cell := match k with
    | .shared => { c with readers := c.readers.erase t }
    | .exclusive => { c with writer := none }
  Spec.bind (Spec.emit (.release a.cell t k)) (fun _ => Spec.pure (s.put a.cell c'))

/-- Deref of a live guard: the current payload of that cell (no event). -/
def payload (a : AccountInfo) (s : SdkState) : Bytes := (s.cells a.cell).payload

/-- `snapshot` (r1_pool_adapter_owned.rs:29-43; CLOSED TX1:343 / TX2:239,
NIM_NHY_SnapshotJoin): shared borrow; on Ok read length, copy (allocation)
only for an admitted length, then drop the guard; on Err keep the error in
both fields. -/
def snapshot (a : AccountInfo) (length1 length2 : Nat) (s : SdkState) :
    Spec (OwnedAccount × SdkState) :=
  Spec.bind (acquire a .shared s) (fun r => match r with
    | (.error e, s1) =>
        Spec.pure (⟨a.key, a.owner, a.is_signer, a.is_writable, a.executable,
          .error e, .error e⟩, s1)
    | (.ok t, s1) =>
        let data := payload a s1
        let n := data.length
        let admitted := n == length1 || n == length2
        Spec.bind (if admitted then Spec.alloc else Spec.pure ()) (fun _ =>
          Spec.bind (release a t .shared s1) (fun s2 =>
            Spec.pure (⟨a.key, a.owner, a.is_signer, a.is_writable, a.executable,
              .ok n, if admitted then .ok data else .error .invalidAccountData⟩, s2))))

end RSL
