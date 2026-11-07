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
    INFALLIBLE allocation site (Box::new, Vec growth, to_vec, format!: ruling
    (bl)(3): allocator internals are outside every obligation, a failure
    aborts).  There is no generic "may abort anywhere" clause, so a
    constant-abort or constant-Err implementation is rejected (each row
    module carries the rejection examples);
  * Revision 3 (ruling (bq), LIB0_ F1): a FALLIBLE reservation
    (`Vec::try_reserve_exact` in heap::filled / heap::uninit, r0/heap.rs:5-14)
    is not an abort site.  Its outcome is the oracle reply `Env.reservation`
    (`Spec.tryReserve`), and its failure is the returned
    `Err(Error::Allocation)`.  A law that reaches only such sites and oracle
    replies is therefore a function of (arguments, Env) (`Spec.Functional`).
Oracle replies (sha256, create_program_address, Clock, and since Revision 3
the reservation reply) come from `Env`, which the RowSpec quantifies
universally; binding them to the runtime is the job of the accepted runtime
rows (ruling (at): the PDA reply is the quantified slot) and of
`TAS.Sig.EnvRep` (the reservation reply is bound there to the headline
`reservation` binder).
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
  /-- Revision 3 (ruling (bq), LIB0_ F1).  Reply of the fallible reservation
  `Vec::try_reserve_exact` reached by heap::filled / heap::uninit
  (r0/heap.rs:5-14 at 4bb3b3f): `true` = `Ok(())`, `false` = `Err(_)`.  Every
  frozen caller discards the TryReserveError payload (`map_err(|_|
  Error::Allocation)`), so a Bool carries all of the reply that is observable.
  It is ONE reply for every try_reserve occurrence, the same shape as the
  headline binder `reservation : NP6_StdModel.Reservation`, which
  `NP6_StdModel.calls` returns at every `reserve` call; `TAS.Sig.EnvRep`
  binds `env.reservation = true ↔ reservation = .Ok ()`.  No event: the
  reservation is not a syscall. -/
  reservation : Bool

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

/-- An infallible allocation site (Box::new, Vec growth, to_vec, format! ...).
Ruling (bl)(3): either the fresh object exists, or the transaction aborts here
with the prefix so far.  Revision 3: heap::filled / heap::uninit are NOT such
sites; their `try_reserve_exact` is `Spec.tryReserve`. -/
def alloc : Spec Unit := fun _ o => o = ⟨.ret (), []⟩ ∨ o = ⟨.abort, []⟩

/-- An allocation site that is reached only when `b` holds (no effect otherwise). -/
def allocIf (b : Bool) : Spec Unit := if b then alloc else Spec.pure ()

/-- A reachable Rust panic (index out of range, unwrap on None, ...). -/
def panic {α : Type} : Spec α := fun _ o => o = ⟨.abort, []⟩

/-- Read a value from the oracle environment, no event. -/
def env {α : Type} (f : Env → α) : Spec α := fun e o => o = ⟨.ret (f e), []⟩

/-- Revision 3 (ruling (bq), LIB0_ F1).  A fallible reservation
`try_reserve_exact` (r0/heap.rs:7, 13): returns the oracle reply
`Env.reservation` (`true` = Ok), no event, no abort. -/
def tryReserve : Spec Bool := env Env.reservation

/-- Revision 3.  `m` is a function of the oracle environment: at every `env`
it admits exactly one observation.  The gate requires this of the laws of
`VLib.filled`, `VLib.accNew`, `VLib.weightsNew`, `VLib.claims` (on their
domains) and `V2Lib.tx2auth` (on `Dom064`) whenever they reach no infallible
allocation site; an infallible site keeps its (bl)(3) abort arm. -/
def Functional {α : Type} (m : Spec α) : Prop :=
  ∀ env, ∃ o, ∀ o', m env o' ↔ o' = o

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

/-- Revision 2 (NMT-S1).  `<ProgramError as Clone>::clone` allocates exactly when
the payload owns heap memory: `BorshIoError(String)` with a nonempty String
(String::clone -> Vec::clone -> `[u8]::to_vec_in`, which allocates `len` bytes and
allocates nothing at `len = 0`; pinned nightly-2026-09-17 std, source excerpts in
evidence/tx1-owned-20261111/NMT_CLONE_STD_SOURCE.json).  Every other variant is
plain data and its clone has no effect. -/
def ProgramError.cloneAllocates : ProgramError → Bool
  | .borshIoError msg => !msg.isEmpty
  | _ => false

/-- `match r { Ok(x) => Ok(x), Err(e) => Err(e.clone()) }` followed by `?`:
the Err arm passes the clone's allocation site (ruling (bl)(3): fresh String or
abort with the prefix so far) before returning the cloned error. -/
def RS.ofCloned {α : Type} (x : Except ProgramError α) : RS α :=
  match x with
  | .ok a => RS.pure a
  | .error e => if e.cloneAllocates then RS.bind (RS.lift Spec.alloc) (fun _ => RS.throw e)
                else RS.throw e

theorem RS.ofCloned_ok {α : Type} (a : α) : (RS.ofCloned (.ok a) : RS α) = RS.pure a := rfl

theorem RS.ofCloned_error {α : Type} (e : ProgramError) (h : e.cloneAllocates = false) :
    (RS.ofCloned (.error e) : RS α) = RS.throw e := by
  simp [RS.ofCloned, h]

/-- On a value whose error (if any) carries no heap payload, the clone is the
plain Result. -/
theorem RS.ofCloned_eq_ofExcept {α : Type} (x : Except ProgramError α)
    (h : ∀ e, x = .error e → e.cloneAllocates = false) : RS.ofCloned x = RS.ofExcept x := by
  cases x with
  | ok a => rfl
  | error e => exact RS.ofCloned_error e (h e rfl)

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


/-- `l[i]` on a slice: panics (abort, prefix only) when out of range. -/
def RS.index {α : Type} (l : List α) (i : Nat) : RS α :=
  match l[i]? with
  | some a => RS.pure a
  | none => RS.lift Spec.panic

theorem Spec.call_trivial {A B : Type} (dom : A → Prop) (law : A → Spec B) (a : A)
    (h : dom a) : Spec.call dom law a = law a := by
  funext env o
  apply propext
  exact ⟨fun hc => hc.2, fun hl => ⟨h, hl⟩⟩


/-- Every observation of `emit ev >>= k` starts with `ev`. -/
theorem Spec.bind_emit_head {β : Type} (ev : Event) (k : Unit → Spec β) (env : Env) (o : Obs β)
    (h : Spec.bind (Spec.emit ev) k env o) : ∃ rest, o.events = ev :: rest := by
  rcases h with ⟨u, e1, o2, hm, _, ho⟩ | ⟨e1, hm, _⟩ | ⟨e1, hm, _⟩
  · simp only [Spec.emit, Obs.mk.injEq] at hm
    rcases hm with ⟨_, rfl⟩
    subst ho
    exact ⟨o2.events, rfl⟩
  · simp [Spec.emit] at hm
  · simp [Spec.emit] at hm


/-- If `m` admits exactly one silent returning observation, `bind m k` is `k`. -/
theorem Spec.bind_det {α β : Type} (m : Spec α) (k : α → Spec β) (env : Env) (x : α)
    (hm : ∀ o, m env o ↔ o = ⟨.ret x, []⟩) (o : Obs β) :
    Spec.bind m k env o ↔ k x env o := by
  constructor
  · intro h
    rcases h with ⟨a, e1, o2, h1, h2, ho⟩ | ⟨e1, h1, _⟩ | ⟨e1, h1, _⟩
    · have := (hm _).mp h1
      simp only [Obs.mk.injEq, Exit.ret.injEq] at this
      rcases this with ⟨rfl, rfl⟩
      subst ho; cases o2; simpa using h2
    · have := (hm _).mp h1; simp at this
    · have := (hm _).mp h1; simp at this
  · intro h
    exact Or.inl ⟨x, [], o, (hm _).mpr rfl, h, by cases o; rfl⟩


/-- Revision 2 helper: if `m` admits exactly one silent return `x` and the silent
abort (an allocation site), `bind m k` is `k x` or that abort. -/
theorem Spec.bind_two {α β : Type} (m : Spec α) (k : α → Spec β) (env : Env) (x : α)
    (hm : ∀ o, m env o ↔ o = ⟨.ret x, []⟩ ∨ o = ⟨.abort, []⟩) (o : Obs β) :
    Spec.bind m k env o ↔ k x env o ∨ o = ⟨.abort, []⟩ := by
  constructor
  · intro h
    rcases h with ⟨a, e1, o2, h1, h2, ho⟩ | ⟨e1, h1, ho⟩ | ⟨e1, h1, ho⟩
    · rcases (hm _).mp h1 with h | h
      · simp only [Obs.mk.injEq, Exit.ret.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        subst ho; left; cases o2; simpa using h2
      · simp at h
    · rcases (hm _).mp h1 with h | h
      · simp at h
      · simp only [Obs.mk.injEq] at h
        rcases h with ⟨_, rfl⟩
        exact Or.inr ho
    · rcases (hm _).mp h1 with h | h <;> simp at h
  · rintro (h | rfl)
    · exact Or.inl ⟨x, [], o, (hm _).mpr (Or.inl rfl), h, by cases o; rfl⟩
    · exact Or.inr (Or.inl ⟨[], (hm _).mpr (Or.inr rfl), rfl⟩)

theorem RS.lift_alloc_iff (env : Env) (o : Obs (Except ProgramError Unit)) :
    RS.lift Spec.alloc env o ↔ o = ⟨.ret (.ok ()), []⟩ ∨ o = ⟨.abort, []⟩ := by
  unfold RS.lift Spec.map
  rw [Spec.bind_two _ _ env () (fun _ => Iff.rfl)]
  rfl

/-- `alloc; k`: exactly the silent allocation abort, or `k`. -/
theorem RS.alloc_seq_iff {β : Type} (k : RS β) (env : Env) (o : Obs (Except ProgramError β)) :
    RS.seq (RS.lift Spec.alloc) k env o ↔ k env o ∨ o = ⟨.abort, []⟩ := by
  unfold RS.seq RS.bind
  rw [Spec.bind_two _ _ env (.ok ()) (RS.lift_alloc_iff env)]

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

/-- Revision 2 teeth: a deferred nonempty BorshIoError makes the getter's clone
arm admit the silent allocation abort; a payload-free error does not. -/
theorem RS.ofCloned_heap_abort {α : Type} (m : String) (hm : m.isEmpty = false) (env : Env) :
    (RS.ofCloned (.error (.borshIoError m)) : RS α) env ⟨.abort, []⟩ := by
  have h : (ProgramError.borshIoError m).cloneAllocates = true := by
    simp [ProgramError.cloneAllocates, hm]
  simp only [RS.ofCloned, h, if_true]
  exact (RS.alloc_seq_iff (RS.throw (.borshIoError m)) env _).mpr (Or.inr rfl)

theorem RS.ofCloned_plain_no_abort {α : Type} (e : ProgramError) (h : e.cloneAllocates = false)
    (env : Env) : ¬ (RS.ofCloned (.error e) : RS α) env ⟨.abort, []⟩ := by
  rw [RS.ofCloned_error e h]
  simp [RS.throw, Spec.pure]

/-- Constant implementations used by every rejection example. -/
def constErr {A α : Type} (e : ProgramError) : A → Env → Obs (Except ProgramError α) :=
  fun _ _ => ⟨.ret (.error e), []⟩

def constAbort {A α : Type} : A → Env → Obs α := fun _ _ => ⟨.abort, []⟩

/-- A default oracle environment for examples (any Env works for the
pre-oracle checks the examples use).  Revision 3: its reservation reply is the
failure `false`, so the heap::filled-Err hypotheses of the TX1:087/094
rejection examples are met by a law that reads `Env.reservation`. -/
def env0 : Env := ⟨fun _ => zero32, fun _ _ => none, .error .unsupportedSysvar, false⟩

/-! ## Owned account snapshot (r1_pool_adapter_owned.rs:9-25) -/

structure OwnedAccount where
  key : B32
  owner : B32
  is_signer : Bool
  is_writable : Bool
  executable : Bool
  length : Except ProgramError Nat
  bytes : Except ProgramError Bytes

/-- `OwnedAccount::data` (r1_pool_adapter_owned.rs:21-23; CLOSED TX1:335 /
TX2:229, NHJ_DataPacket) followed by `?`: Ok(&bytes), or Err(error.clone()).
Revision 2 (NMT-S1): the clone of a heap-carrying error is an allocation site
(`RS.ofCloned`); no other effect. -/
def OwnedAccount.data (a : OwnedAccount) : RS Bytes := RS.ofCloned a.bytes
/-- `OwnedAccount::data_len` (line 24, `self.length.clone()`) followed by `?`. -/
def OwnedAccount.data_len (a : OwnedAccount) : RS Nat := RS.ofCloned a.length

/-- The deferred errors that `snapshot` can store (r1_pool_adapter_owned.rs:29-43):
the SDK borrow error AccountBorrowFailed in both fields, or InvalidAccountData in
`bytes` for a non-admitted length.  Proved for every snapshot observation in
RSL_TX1_344 (`snapshot_errs`, `snapAll_errs`); used there to show the clone
allocation arms of Revision 2 are unreachable at the actual callers. -/
def OwnedAccount.SnapshotErrs (a : OwnedAccount) : Prop :=
  (∀ e, a.length = .error e → e = .accountBorrowFailed) ∧
  (∀ e, a.bytes = .error e → e = .accountBorrowFailed ∨ e = .invalidAccountData)

theorem OwnedAccount.data_of_snapshotErrs (a : OwnedAccount) (h : a.SnapshotErrs) :
    a.data = RS.ofExcept a.bytes := by
  apply RS.ofCloned_eq_ofExcept
  intro e he
  rcases h.2 e he with rfl | rfl <;> rfl

theorem OwnedAccount.data_len_of_snapshotErrs (a : OwnedAccount) (h : a.SnapshotErrs) :
    a.data_len = RS.ofExcept a.length := by
  apply RS.ofCloned_eq_ofExcept
  intro e he
  rw [h.1 e he]; rfl

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
and its (cloned) Err is returned unchanged.  Revision 2: RS-valued, because the
`data_len` clone is an allocation site for a heap-carrying error. -/
def verifierCheckpoint (a : OwnedAccount) (program : B32) (writable : Bool) : RS Unit :=
  if decide (a.owner ≠ program) || a.is_signer || a.executable || a.is_writable != writable then
    RS.throw .invalidAccountData
  else RS.bind a.data_len fun n => RS.check (n != CHECKPOINT_BYTES) .invalidAccountData

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


/-- Nonempty event logs propagate through `bind` from the first step. -/
theorem Spec.bind_nonempty {α β : Type} (m : Spec α) (k : α → Spec β) (env : Env) (o : Obs β)
    (hm : ∀ o', m env o' → o'.events ≠ []) (h : Spec.bind m k env o) : o.events ≠ [] := by
  rcases h with ⟨a, e1, o2, h1, _, ho⟩ | ⟨e1, h1, ho⟩ | ⟨e1, h1, ho⟩
  · subst ho; have := hm _ h1; simp only at this ⊢; intro hc
    exact this (List.append_eq_nil_iff.mp hc).1
  · subst ho; exact hm _ h1
  · subst ho; exact hm _ h1

theorem Spec.emit_bind_nonempty {β : Type} (ev : Event) (k : Unit → Spec β) (env : Env) (o : Obs β)
    (h : Spec.bind (Spec.emit ev) k env o) : o.events ≠ [] := by
  obtain ⟨rest, hr⟩ := Spec.bind_emit_head ev k env o h
  rw [hr]; exact List.cons_ne_nil _ _

theorem acquire_nonempty (a : AccountInfo) (k : Kind) (s : SdkState) (env : Env)
    (o : Obs (Except ProgramError Nat × SdkState)) (h : acquire a k s env o) : o.events ≠ [] := by
  unfold acquire at h
  cases k <;> (simp only at h; split at h <;> exact Spec.emit_bind_nonempty _ _ _ _ h)

theorem snapshot_nonempty (a : AccountInfo) (l1 l2 : Nat) (s : SdkState) (env : Env)
    (o : Obs (OwnedAccount × SdkState)) (h : snapshot a l1 l2 s env o) : o.events ≠ [] :=
  Spec.bind_nonempty _ _ _ _ (fun o' h' => acquire_nonempty a .shared s env o' h') h

/-! ## Revision 3 teeth (ruling (bq), LIB0_ F1) -/

theorem Spec.tryReserve_functional : Spec.Functional Spec.tryReserve :=
  fun env => ⟨⟨.ret env.reservation, []⟩, fun _ => Iff.rfl⟩

/-- The reply is read, not chosen: at a fixed Env exactly one arm is admitted. -/
theorem Spec.tryReserve_iff (env : Env) (o : Obs Bool) :
    Spec.tryReserve env o ↔ o = ⟨.ret env.reservation, []⟩ := Iff.rfl

/-- A law of the heap::filled shape that reads the reply
(`Ok(vec![v; n])` on Ok, `Err(())` otherwise; `resize` after a successful
reservation does not allocate) is a function of Env. -/
theorem Spec.functional_of_reserve {α : Type} (okv : α) (errv : α) :
    Spec.Functional (Spec.bind Spec.tryReserve
      (fun b => if b then Spec.pure okv else Spec.pure errv)) := by
  intro env
  refine ⟨⟨.ret (if env.reservation then okv else errv), []⟩, fun o => ?_⟩
  rw [Spec.bind_det _ _ env env.reservation (Spec.tryReserve_iff env)]
  cases env.reservation <;> rfl

/-- Rejection: the Revision 2 relational shape (both arms admitted at the same
Env, the only option while Env had no reservation channel) is not Functional. -/
theorem Spec.not_functional_both {α : Type} (okv errv : α) (hne : okv ≠ errv) :
    ¬ Spec.Functional (fun (_ : Env) (o : Obs α) => o = ⟨.ret okv, []⟩ ∨ o = ⟨.ret errv, []⟩) := by
  intro h
  obtain ⟨o, ho⟩ := h env0
  have h1 := (ho ⟨.ret okv, []⟩).mp (Or.inl rfl)
  have h2 := (ho ⟨.ret errv, []⟩).mp (Or.inr rfl)
  rw [← h2] at h1
  simp only [Obs.mk.injEq, Exit.ret.injEq] at h1
  exact hne h1.1

end RSL
