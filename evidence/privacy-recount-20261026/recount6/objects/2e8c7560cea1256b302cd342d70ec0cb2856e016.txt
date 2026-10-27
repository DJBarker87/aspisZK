import R1Z.ProverCommitEntropy34
import R1Z.ProverCommitRetry34

/-! D147 environment. The schedule sees only primitive call tags and their
return statuses. Neither random bytes, file payloads, nonce paths nor witness
values occur in its carrier. Private ledger entries survive partial writes,
failed fsync and subsequent protocol rejection. These are execution-model
facts; native source correspondence is a separate obligation. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitEnvironment35
open R0Z.FsStatement ProverCommitEntropy18 ProverCommitEntropyJoin18
abbrev Secret := R1Z.GamesR1PBin.SecP

inductive Kind where
  | rng | create | writeMagic | writeDigest | writeNonce
  | fileSync | directoryOpen | directorySync
  deriving DecidableEq, Repr

inductive IOError where
  | alreadyExists | other : Nat → IOError
  deriving DecidableEq, Repr

abbrev Outcome := Except IOError Unit
abbrev Event := Kind × Outcome
abbrev History := List Event

/-- Index is the complete primitive-call count, including failed calls.
The caller supplies no byte-valued input to this function. -/
abbrev Schedule := Nat → Kind → History → Outcome

structure State where
  history : History
  cursor : Nat
  burned : List OracleAnswer

def ask (schedule : Schedule) (kind : Kind) (s : State) : Outcome × State :=
  let result := schedule s.history.length kind s.history
  (result, {s with history := s.history ++ [(kind,result)]})

theorem ask_blind (schedule : Schedule) (kind : Kind) (a b : State)
    (same : a.history = b.history) :
    (ask schedule kind a).1 = (ask schedule kind b).1 := by
  simp only [ask, same]

theorem ask_retains (schedule : Schedule) (kind : Kind) (s : State) :
    (ask schedule kind s).2.burned = s.burned ∧
    (ask schedule kind s).2.cursor = s.cursor := ⟨rfl,rfl⟩

def ioChain (schedule : Schedule) : List Kind → State → Outcome × State
  | [], s => (.ok (),s)
  | kind::rest, s =>
    let step := ask schedule kind s
    match step.1 with
    | .error e => (.error e,step.2)
    | .ok _ => ioChain schedule rest step.2

theorem chain_retains (schedule : Schedule) (kinds : List Kind) (s : State) :
    (ioChain schedule kinds s).2.burned = s.burned := by
  induction kinds generalizing s with
  | nil => rfl
  | cons kind rest ih =>
    cases h : (ask schedule kind s).1 with
    | error e => simp only [ioChain,h]; rfl
    | ok u =>
      simp only [ioChain,h]
      exact ih (ask schedule kind s).2

inductive ReservationError where
  | duplicate | io : IOError → ReservationError
  deriving DecidableEq, Repr

/-- Unix directory open is a fallible primitive too; non-Unix matches the
source's no-op sync_directory branch. No file is removed on any branch. -/
def writes (unix : Bool) : List Kind :=
  [.writeMagic,.writeDigest,.writeNonce,.fileSync] ++
    if unix then [.directoryOpen,.directorySync] else []

def reserve (schedule : Schedule) (unix : Bool) (nonce : OracleAnswer)
    (s : State) : Except ReservationError Unit × State :=
  let step := ask schedule .create s
  match step.1 with
  | .error .alreadyExists => (.error .duplicate,step.2)
  | .error e => (.error (.io e),step.2)
  | .ok _ =>
    let retained := {step.2 with burned := nonce :: step.2.burned}
    let (result,final) := ioChain schedule (writes unix) retained
    (result.mapError ReservationError.io, final)

theorem create_retained (schedule : Schedule) (unix : Bool)
    (nonce : OracleAnswer) (s : State)
    (created : (ask schedule .create s).1 = .ok ()) :
    (reserve schedule unix nonce s).2.burned = nonce :: s.burned := by
  simp only [reserve,created]
  exact chain_retains schedule (writes unix) _

theorem create_failed (schedule : Schedule) (unix : Bool)
    (nonce : OracleAnswer) (s : State) (error : IOError)
    (failed : (ask schedule .create s).1 = .error error) :
    (reserve schedule unix nonce s).2.burned = s.burned := by
  cases error <;> simp only [reserve,failed] <;> rfl

/-- RNG call status is public to the scheduler; the successful bytes come
from a separate private tape, never from the schedule. -/
def next (schedule : Schedule) (tape : Nat → Candidate) (s : State) :
    Except IOError Candidate × State :=
  let (result,after) := ask schedule .rng s
  match result with
  | .error e => (.error e,after)
  | .ok _ => (.ok (tape s.cursor),{after with cursor := s.cursor+1})

/-- E1 specifies the law of each successful raw 96-byte RNG return,
conditional on arbitrary prior context, hence independent of that context.
Context must include the complete prior private and public execution state.
No availability or filesystem-success hypothesis is included. -/
def E1 {Context : Type} (okLaw : Context → Candidate → ℚ) : Prop :=
  ∀ context bytes, okLaw context bytes = 1 / (Fintype.card Candidate : ℚ)

inductive Error where
  | entropy : ProverCommitEntropy18.Error IOError → Error
  | reservation : ReservationError → Error

def prepare (schedule : Schedule) (tape : Nat → Candidate) (unix : Bool)
    (s : State) : Except Error Secret × State :=
  let (generated,after) := generate (next schedule tape) s
  match generated with
  | .error e => (.error (.entropy e),after)
  | .ok secret =>
    let (result,final) := reserve schedule unix (secret 0).val after
    (result.map (fun _ => secret) |>.mapError Error.reservation,final)

/-- Full internal state is passed into the successful continuation. A failed
environment step cannot call derivation or publication, for any witness. -/
def withPrepared {Witness Proof : Type} (schedule : Schedule)
    (tape : Nat → Candidate) (unix : Bool) (s : State) (w : Witness)
    (continuation : Witness → Secret → State → Except Error Proof × State) :
    Except Error Proof × State :=
  match prepare schedule tape unix s with
  | (.error error,after) => (.error error,after)
  | (.ok secret,after) => continuation w secret after

/-- D143/D147 view: success returns proof bytes; failure returns only its
error tag. Internal ledger, RNG bytes and call history are never projected. -/
def observable {Proof : Type} (result : Except Error Proof × State) := result.1

theorem fail_closed {Witness Proof : Type} (schedule : Schedule)
    (tape : Nat → Candidate) (unix : Bool) (s after : State) (e : Error)
    (failed : prepare schedule tape unix s = (.error e,after))
    (w : Witness)
    (continuation : Witness → Secret → State → Except Error Proof × State) :
    withPrepared schedule tape unix s w continuation = (.error e,after) := by
  simp only [withPrepared,failed]

/-- Same schedule and private coins couple the real environment prefix to a
witness-free simulator prefix. This is pointwise, for every failure schedule;
there is no OS/fs probability charge. E1 is needed only for the coins' law. -/
theorem failure_replay {Witness Proof : Type} (schedule : Schedule)
    (tape : Nat → Candidate) (unix : Bool) (s after : State) (e : Error)
    (failed : prepare schedule tape unix s = (.error e,after))
    (w : Witness)
    (real : Witness → Secret → State → Except Error Proof × State)
    (ideal : Unit → Secret → State → Except Error Proof × State) :
    observable (withPrepared schedule tape unix s w real) =
      observable (withPrepared schedule tape unix s () ideal) := by
  rw [fail_closed schedule tape unix s after e failed w real,
    fail_closed schedule tape unix s after e failed () ideal]

#print axioms ask_blind
#print axioms ask_retains
#print axioms chain_retains
#print axioms create_retained
#print axioms create_failed
#print axioms fail_closed
#print axioms failure_replay
end R1Z.ProverCommitEnvironment35
