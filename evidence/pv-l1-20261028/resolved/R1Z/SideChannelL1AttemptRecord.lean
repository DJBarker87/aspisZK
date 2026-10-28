import R1Z.ProverCommitRetryOwner42
import R1Z.ProverCommitTLS23

/-! L1 observation carrier for the selected native route. This is an
instrumented reference, not an extraction certificate for every Rust callee.
Bytes written to the ledger are public; RNG seed bytes are never observations.
Underlying write calls (including partial writes/Interrupted) are retained. -/
set_option autoImplicit false
namespace R1Z.SideChannelL1AttemptRecord
open Aeneas Aeneas.Std Result
abbrev Bytes := List UInt8
abbrev Error := ProverCommitRetry34.Error

inductive Call where
  | callback | rng | publicBytes | context | reservationCreate
  | reservationWrite (part : Fin 3) | reservationFileSync
  | reservationDirectoryOpen | reservationDirectorySync
  | maskDerivation | dDerivation | saltDerivation | maskApply | balanceAudit
  | semanticCanonical | commitment | pole | helper | boundary (round : Nat)
  | terminal | equalCircle | queryScan | checker | compact | opening | publication
  deriving DecidableEq, Repr

/-- Preserve the outer API label as well as the originating call/detail.
A pole and a checker refusal both map to Rejected but remain distinct here. -/
structure Failure where
  call : Call
  detail : String
  label : Error

inductive IOStatus where
  | ok | error (kind : String) | alreadyExists
  deriving DecidableEq, Repr

structure TraceValue where
  tag : UInt16
  index : Nat
  bytes : Fin 32 → UInt8
  deriving DecidableEq

inductive Event where
  | call (site : Call) (ordinal : Nat)
  | rngReturn (status : IOStatus) -- request size is always 64
  | createReturn (publicPath : Bytes) (status : IOStatus)
  | writeReturn (part : Fin 3) (requested : Bytes) (written : Nat) (status : IOStatus)
  | syncReturn (site : Call) (status : IOStatus)
  | failure (origin : Failure)
  | checkerReturn (accepted : Bool) -- one CHECK_TIMES push, magnitudes excluded
  | tracePush (value : TraceValue)
  | traceTake (values : List TraceValue)
  | checkTimesTake (count : Nat)
  | sendOrWrite (site : Call) (bytes : Bytes) (status : IOStatus)

structure TLS where
  values : List TraceValue
  checks : Nat
  deriving DecidableEq

def applyEvent (s : TLS) : Event → TLS
  | .checkerReturn _ => {s with checks := s.checks+1}
  | .tracePush value => {s with values := s.values ++ [value]}
  | .traceTake _ => {s with values := []}
  | .checkTimesTake _ => {s with checks := 0}
  | _ => s

def replayTLS (s : TLS) (events : List Event) : TLS := events.foldl applyEvent s

structure Attempt (Proof : Type) where
  events : List Event
  result : ProverCommitRetry34.Step Proof

/-- Complete terminating run: ordered attempt prefixes and a return count
only on success. Backend divergence/panic requires a separate runtime model. -/
structure Run (Proof : Type) where
  attempts : List (Attempt Proof)
  result : ProverCommitRetry34.Step (ProverCommitRetry34.Published Proof)

abbrev Owner (State Proof : Type) := Nat → State → Attempt Proof × State

def run {State Proof : Type} (owner : Owner State Proof) : Nat → Nat → State → Run Proof × State
  | 0, _, s => (⟨[],.stop .AttemptsExhausted⟩,s)
  | fuel+1, index, s =>
    let (record,after) := owner index s
    match record.result with
    | .done proof => (⟨[record],.done ⟨proof,index+1⟩⟩,after)
    | .stop e => (⟨[record],.stop e⟩,after)
    | .retry =>
      let (rest,final) := run owner fuel (index+1) after
      (⟨record::rest.attempts,rest.result⟩,final)

def events {Proof : Type} (r : Run Proof) := r.attempts.flatMap Attempt.events

/-- Requested L1 projections are derived from the retained event order,
so a later take cannot erase earlier records from the per-run observation. -/
def rngStatuses {Proof : Type} (r : Run Proof) : List IOStatus :=
  (events r).filterMap (fun | .rngReturn status => some status | _ => none)

def rngCallCount {Proof : Type} (r : Run Proof) := (rngStatuses r).length

def checkerInvocations {Proof : Type} (r : Run Proof) : Nat :=
  ((events r).filterMap (fun | .call .checker n => some n | _ => none)).length

def failures {Proof : Type} (r : Run Proof) : List Failure :=
  (events r).filterMap (fun | .failure origin => some origin | _ => none)

def returnedAttempts {Proof : Type} (r : Run Proof) : Option Nat :=
  match r.result with
  | .done published => some published.attempts
  | _ => none

def observedTLS {Proof : Type} (initial : TLS) (r : Run Proof) := replayTLS initial (events r)

/-- The richer owner erases to the existing source-control owner, preserving
all state updates; this does not assert that a native event producer exists. -/
def eraseOwner {State Proof : Type} (owner : Owner State Proof) : ProverCommitRetry34.Attempt State Proof :=
  fun index s => let (record,after) := owner index s; ok (record.result,after)

theorem erase_run {State Proof : Type} (owner : Owner State Proof)
    (fuel index : Nat) (s : State) :
    ProverCommitRetry34.run (eraseOwner owner) fuel index s =
      ok ((run owner fuel index s).1.result,(run owner fuel index s).2) := by
  induction fuel generalizing index s with
  | zero => rfl
  | succ fuel ih =>
    unfold run ProverCommitRetry34.run eraseOwner
    cases h : owner index s with
    | mk record after =>
      simp only [bind_tc_ok]
      cases hr : record.result with
      | done proof => rfl
      | stop error => rfl
      | retry => exact ih (index+1) after

/-- A rejected prefix is retained verbatim before the next callback. -/
theorem rejected_prefix {State Proof : Type} (owner : Owner State Proof)
    (fuel index : Nat) (s after : State) (record : Attempt Proof)
    (step : owner index s = (record,after)) (reject : record.result = .retry) :
    run owner (fuel+1) index s =
      let (rest,final) := run owner fuel (index+1) after
      (⟨record::rest.attempts,rest.result⟩,final) := by
  simp only [run,step,reject]

theorem stopping_prefix {State Proof : Type} (owner : Owner State Proof)
    (fuel index : Nat) (s after : State) (record : Attempt Proof) (e : Error)
    (step : owner index s = (record,after)) (stop : record.result = .stop e) :
    run owner (fuel+1) index s = (⟨[record],.stop e⟩,after) := by
  simp only [run,step,stop]

theorem success_prefix {State Proof : Type} (owner : Owner State Proof)
    (fuel index : Nat) (s after : State) (record : Attempt Proof) (proof : Proof)
    (step : owner index s = (record,after)) (done : record.result = .done proof) :
    run owner (fuel+1) index s = (⟨[record],.done ⟨proof,index+1⟩⟩,after) := by
  simp only [run,step,done]

theorem attempt_cap {State Proof : Type} (owner : Owner State Proof)
    (fuel index : Nat) (s : State) : (run owner fuel index s).1.attempts.length ≤ fuel := by
  induction fuel generalizing index s with
  | zero => exact Nat.le_refl 0
  | succ fuel ih =>
    simp only [run]
    cases h : owner index s with
    | mk record after =>
      cases hr : record.result <;> simp only [List.length_cons,List.length_nil]
      · omega
      · exact Nat.succ_le_succ (ih (index+1) after)
      · omega

/-- Callback Err(Rejected) aborts too: next_attempt(k)? is outside the match.
It must not be passed through classify (which would turn it into retry). -/
def callbackStep {Proof : Type} (e : Error) : ProverCommitRetry34.Step Proof := .stop e

theorem callback_rejected_stops {Proof : Type} :
    callbackStep (Proof := Proof) .Rejected = .stop .Rejected := rfl

theorem tls_retained {Proof : Type} (initial : TLS) (r : Run Proof)
    (noEvents : events r = []) : observedTLS initial r = initial := by
  simp only [observedTLS,noEvents,replayTLS,List.foldl_nil]

theorem returned_count_success {Proof : Type} (r : Run Proof)
    (published : ProverCommitRetry34.Published Proof) (success : r.result = .done published) :
    returnedAttempts r = some published.attempts := by simp only [returnedAttempts,success]

theorem tls_trace_push (s : TLS) (x : TraceValue) :
    replayTLS s [.tracePush x] = ⟨s.values ++ [x],s.checks⟩ := rfl

theorem tls_check_push (s : TLS) (accepted : Bool) :
    replayTLS s [.checkerReturn accepted] = ⟨s.values,s.checks+1⟩ := rfl

#print axioms erase_run
#print axioms rejected_prefix
#print axioms stopping_prefix
#print axioms success_prefix
#print axioms attempt_cap
#print axioms callback_rejected_stops
#print axioms tls_retained
#print axioms returned_count_success
#print axioms tls_trace_push
#print axioms tls_check_push
end R1Z.SideChannelL1AttemptRecord
