import R1Z.ProverCommitEnvironment35

/-! D148 private reservation membership model. Faults and added paths are
chosen without private bytes. This component specifies membership/retention;
it does not certify the native SHA-256 address distribution or file contents. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitLedger36
open R0Z.FsStatement ProverCommitEntropy18 ProverCommitEnvironment35
attribute [local instance] Classical.propDecidable

abbrev Path := OracleAnswer
abbrev Ledger := List Path

structure Action where
  fault : Option Nat
  additions : List Path

/-- No nonce, address, ledger, payload, witness or successful RNG bytes are
arguments. The initial ledger is chosen separately, before the private tape. -/
abbrev Schedule := Nat → Kind → History → Action

structure State where
  history : History
  cursor : Nat
  ledger : Ledger

def inject (a : Action) (s : State) : State :=
  {s with ledger := s.ledger ++ a.additions}

def record (kind : Kind) (result : Outcome) (s : State) : Outcome × State :=
  (result, {s with history := s.history ++ [(kind,result)]})

def faultResult (a : Action) : Outcome :=
  match a.fault with
  | none => .ok ()
  | some e => .error (.other e)

def ask (schedule : Schedule) (kind : Kind) (s : State) : Outcome × State :=
  let a := schedule s.history.length kind s.history
  record kind (faultResult a) (inject a s)

/-- Membership is private, not a schedule decision. An occupied path always
returns AlreadyExists. A fresh path may fail before atomic creation. Entries
are never deleted, including on partial-write/fsync failures. -/
def createNew (path : Path) (a : Action) (s : State) : Outcome × State :=
  let t := inject a s
  if path ∈ t.ledger then record .create (.error .alreadyExists) t
  else match a.fault with
  | some e => record .create (.error (.other e)) t
  | none => record .create (.ok ()) {t with ledger := path :: t.ledger}

theorem alreadyExists_iff (path : Path) (a : Action) (s : State) :
    (createNew path a s).1 = .error .alreadyExists ↔ path ∈ (inject a s).ledger := by
  by_cases h : path ∈ (inject a s).ledger
  · simp [createNew,h,record]
  · cases hf : a.fault <;> simp [createNew,h,hf,record]

theorem create_preserves (path old : Path) (a : Action) (s : State)
    (present : old ∈ s.ledger) : old ∈ (createNew path a s).2.ledger := by
  have h : old ∈ (inject a s).ledger := List.mem_append_left _ present
  by_cases hp : path ∈ (inject a s).ledger
  · simpa [createNew,hp,record] using h
  · cases hf : a.fault <;> simp [createNew,hp,hf,record,h]

theorem created_present (path : Path) (a : Action) (s : State)
    (ok : (createNew path a s).1 = .ok ()) :
    path ∈ (createNew path a s).2.ledger := by
  by_cases hp : path ∈ (inject a s).ledger
  · simp [createNew,hp,record] at ok
  · cases hf : a.fault <;> simp_all [createNew,record]

def ioChain (schedule : Schedule) : List Kind → State → Outcome × State
  | [], s => (.ok (),s)
  | kind::rest, s =>
    let step := ask schedule kind s
    match step.1 with
    | .error e => (.error e,step.2)
    | .ok _ => ioChain schedule rest step.2

theorem chain_preserves (schedule : Schedule) (kinds : List Kind)
    (s : State) (path : Path) (present : path ∈ s.ledger) :
    path ∈ (ioChain schedule kinds s).2.ledger := by
  induction kinds generalizing s with
  | nil => exact present
  | cons kind rest ih =>
    have h : path ∈ (ask schedule kind s).2.ledger :=
      List.mem_append_left _ present
    cases he : (ask schedule kind s).1 with
    | error e => simp only [ioChain,he]; exact h
    | ok u => simp only [ioChain,he]; exact ih _ h

def reserve (schedule : Schedule) (unix : Bool) (path : Path) (s : State) :
    Except ReservationError Unit × State :=
  let a := schedule s.history.length .create s.history
  let step := createNew path a s
  match step.1 with
  | .error .alreadyExists => (.error .duplicate,step.2)
  | .error e => (.error (.io e),step.2)
  | .ok _ =>
    let (result,after) := ioChain schedule (writes unix) step.2
    (result.mapError ReservationError.io,after)

theorem reservation_retained (schedule : Schedule) (unix : Bool)
    (path : Path) (s : State)
    (ok : (createNew path (schedule s.history.length .create s.history) s).1 = .ok ()) :
    path ∈ (reserve schedule unix path s).2.ledger := by
  simp only [reserve,ok]
  exact chain_preserves schedule (writes unix) _ path
    (created_present path _ s ok)

theorem duplicate_path (schedule : Schedule) (unix : Bool) (path : Path)
    (s : State) (present : path ∈ s.ledger) :
    (reserve schedule unix path s).1 = .error .duplicate := by
  have h : (createNew path (schedule s.history.length .create s.history) s).1 =
      .error .alreadyExists := (alreadyExists_iff _ _ _).2
        (List.mem_append_left _ present)
  simp only [reserve,h]

def next (schedule : Schedule) (tape : Nat → Candidate) (s : State) :
    Except IOError Candidate × State :=
  let (result,after) := ask schedule .rng s
  match result with
  | .error e => (.error e,after)
  | .ok _ => (.ok (tape s.cursor),{after with cursor := s.cursor+1})

def prepare (address : Path → Path) (schedule : Schedule)
    (tape : Nat → Candidate) (unix : Bool) (s : State) :
    Except ProverCommitEnvironment35.Error Secret × State :=
  let (generated,after) := generate (next schedule tape) s
  match generated with
  | .error e => (.error (.entropy e),after)
  | .ok secret =>
    let (result,final) := reserve schedule unix (address (secret 0).val) after
    (result.map (fun _ => secret) |>.mapError
      ProverCommitEnvironment35.Error.reservation,final)

def withPrepared {Witness Proof : Type} (address : Path → Path)
    (schedule : Schedule) (tape : Nat → Candidate) (unix : Bool) (s : State)
    (w : Witness) (continuation : Witness → Secret → State →
      Except ProverCommitEnvironment35.Error Proof × State) :
    Except ProverCommitEnvironment35.Error Proof × State :=
  match prepare address schedule tape unix s with
  | (.error e,after) => (.error e,after)
  | (.ok secret,after) => continuation w secret after

theorem fail_closed {Witness Proof : Type} (address : Path → Path)
    (schedule : Schedule) (tape : Nat → Candidate) (unix : Bool)
    (s after : State) (e : ProverCommitEnvironment35.Error)
    (failed : prepare address schedule tape unix s = (.error e,after))
    (w : Witness) (continuation : Witness → Secret → State →
      Except ProverCommitEnvironment35.Error Proof × State) :
    withPrepared address schedule tape unix s w continuation = (.error e,after) := by
  simp only [withPrepared,failed]

theorem failure_replay {Witness Proof : Type} (address : Path → Path)
    (schedule : Schedule) (tape : Nat → Candidate) (unix : Bool)
    (s after : State) (e : ProverCommitEnvironment35.Error)
    (failed : prepare address schedule tape unix s = (.error e,after))
    (w : Witness)
    (real : Witness → Secret → State → Except ProverCommitEnvironment35.Error Proof × State)
    (ideal : Unit → Secret → State → Except ProverCommitEnvironment35.Error Proof × State) :
    (withPrepared address schedule tape unix s w real).1 =
      (withPrepared address schedule tape unix s () ideal).1 := by
  rw [fail_closed address schedule tape unix s after e failed w real,
    fail_closed address schedule tape unix s after e failed () ideal]

/-- Named environment trust item E2. The native implementation must instantiate
this contract; this definition is not an axiom or a claim of that instance.
`stored` describes durable data, and `persists` includes all future faults. -/
structure E2 (OS Data : Type) (present : OS → Path → Prop)
    (create : OS → Path → Outcome × OS)
    (stored : OS → Path → Data → Prop)
    (writtenFsynced : OS → Path → Data → OS → Prop)
    (persists : OS → OS → Prop) : Prop where
  atomic : ∀ s p, ((create s p).1 = .error .alreadyExists ↔ present s p) ∧
    ((create s p).1 = .ok () → present (create s p).2 p) ∧
    (∀ q, present s q → present (create s p).2 q)
  durable : ∀ s p data t, writtenFsynced s p data t →
    stored t p data ∧ ∀ u, persists t u → stored u p data

#print axioms alreadyExists_iff
#print axioms create_preserves
#print axioms created_present
#print axioms chain_preserves
#print axioms reservation_retained
#print axioms duplicate_path
#print axioms fail_closed
#print axioms failure_replay
end R1Z.ProverCommitLedger36
