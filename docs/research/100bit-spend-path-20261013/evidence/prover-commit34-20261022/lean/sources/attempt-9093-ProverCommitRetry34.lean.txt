import R1Z.ProverCommitDomain34
import R1Z.ProverCommitNative30
/-! Stateful retry/publication control. Callbacks retain the full oracle,
entropy and durable-store state. This file does not assert their source laws;
the actual serializer is installed, and the native walk is transported below.
Only Rejected retries; all other errors, backend failure and divergence stop.
No rejected attempt returns a proof. -/
set_option autoImplicit false
namespace R1Z.ProverCommitRetry34
open Aeneas Aeneas.Std Result
open AspisR1SimControl21
abbrev Error := verifier.Error
abbrev Status (P : Type) := core.result.Result P Error
inductive Step (P : Type) where
  | done : P → Step P
  | retry : Step P
  | stop : Error → Step P

abbrev Attempt (S P : Type) := Nat → S → Result (Step P × S)
abbrev Entropy (S Secret : Type) := Nat → S → Result (Status Secret × S)

def classify {P : Type} : Status P → Step P
  | .Ok p => .done p
  | .Err .Rejected => .retry
  | .Err e => .stop e

structure Published (P : Type) where
  proof : P
  attempts : Nat

def run {S P : Type} (attempt : Attempt S P) :
    Nat → Nat → S → Result (Step (Published P) × S)
  | 0, _, state => ok (.stop .AttemptsExhausted,state)
  | fuel+1, index, state => do
    let (result,after) ← attempt index state
    match result with
    | .done proof => ok (.done ⟨proof,index+1⟩,after)
    | .retry => run attempt fuel (index+1) after
    | .stop e => ok (.stop e,after)

def eight {S P : Type} (attempt : Attempt S P) (state : S) :=
  run attempt 8 0 state

/-- Publication projection used by D143: internal attempt count is erased. -/
def published {S P : Type} : Result (Step (Published P) × S) → Option P
  | .ok (.done p,_) => some p.proof
  | _ => none

def NoProof {S P : Type} (r : Result (Step P × S)) : Prop :=
  ∀ proof after, r ≠ ok (.done proof,after)

/-- Exact extracted serializer guard precedes every continuation that can
reserve, derive masks or construct proof bytes in prove_masked_attempt. -/
def checked {S P : Type} (pub : ProverCommitDomain34.Source)
    (continuation : ProverCommitDomain34.SourceBytes → S → Result (Status P × S))
    (state : S) : Result (Step P × S) := do
  let bytes ← AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes pub
  match bytes with
  | .Err _ => ok (.stop .Semantic,state)
  | .Ok bytes => do
    let (status,after) ← continuation bytes state
    ok (classify status,after)

/-- The entropy callback is invoked before the pub guard, as in the
shipped prove_masked_retrying_with, and its returned state is retained. -/
def realAttempt {S Secret P : Type}
    (pub : ProverCommitDomain34.Source)
    (entropy : Entropy S Secret)
    (continuation : Secret → ProverCommitDomain34.SourceBytes → S → Result (Status P × S)) :
    Attempt S P := fun index state => do
  let (result,after) ← entropy index state
  match result with
  | .Err e => ok (.stop e,after)
  | .Ok secret => checked pub (continuation secret) after

theorem checked_outside {S P : Type} (pub : ProverCommitDomain34.Source)
    (hx : ¬ ProverCommitDomain34.DeployedStatement (ProverCommitDomain34.sourceImage pub))
    (continuation : ProverCommitDomain34.SourceBytes → S → Result (Status P × S))
    (state : S) : NoProof (checked pub continuation state) := by
  unfold checked
  cases hs : AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes pub with
  | fail e => intro proof after impossible; cases impossible
  | div => intro proof after impossible; cases impossible
  | ok result =>
    cases result with
    | Err e => intro proof after impossible; cases impossible
    | Ok bytes => exact False.elim (hx ⟨pub,bytes,rfl,hs⟩)

theorem real_outside {S Secret P : Type}
    (pub : ProverCommitDomain34.Source)
    (hx : ¬ ProverCommitDomain34.DeployedStatement (ProverCommitDomain34.sourceImage pub))
    (entropy : Entropy S Secret)
    (continuation : Secret → ProverCommitDomain34.SourceBytes → S → Result (Status P × S))
    (index : Nat) (state : S) : NoProof (realAttempt pub entropy continuation index state) := by
  unfold realAttempt
  cases he : entropy index state with
  | fail e => intro proof after impossible; cases impossible
  | div => intro proof after impossible; cases impossible
  | ok pair =>
    rcases pair with ⟨result,after⟩
    cases result with
    | Err e => intro proof after impossible; cases impossible
    | Ok secret => exact checked_outside pub hx (continuation secret) after

theorem run_no_proof {S P : Type} (attempt : Attempt S P)
    (none : ∀ index state, NoProof (attempt index state))
    (fuel index : Nat) (state : S) : NoProof (run attempt fuel index state) := by
  induction fuel generalizing index state with
  | zero => intro proof after impossible; cases impossible
  | succ fuel ih =>
    unfold run
    cases ha : attempt index state with
    | fail e => intro proof after impossible; cases impossible
    | div => intro proof after impossible; cases impossible
    | ok pair =>
      rcases pair with ⟨result,after⟩
      cases result with
      | done proof => exact False.elim (none index state proof after ha)
      | retry => exact ih (index+1) after
      | stop e => intro proof after impossible; cases impossible

theorem outside_nothing_published {S Secret P : Type}
    (pub : ProverCommitDomain34.Source)
    (hx : ¬ ProverCommitDomain34.DeployedStatement (ProverCommitDomain34.sourceImage pub))
    (entropy : Entropy S Secret)
    (continuation : Secret → ProverCommitDomain34.SourceBytes → S → Result (Status P × S))
    (state : S) : published (eight (realAttempt pub entropy continuation) state) = none := by
  have hn := run_no_proof (realAttempt pub entropy continuation)
    (real_outside pub hx entropy continuation) 8 0 state
  unfold eight
  cases hr : run (realAttempt pub entropy continuation) 8 0 state with
  | fail _ => rfl
  | div => rfl
  | ok pair =>
    rcases pair with ⟨result,after⟩
    cases result with
    | stop _ => rfl
    | retry => rfl
    | done proof => exact False.elim (hn proof after hr)

/-- A rejection retains every state update and advances the attempt index. -/
theorem rejected_next {S P : Type} (attempt : Attempt S P)
    (fuel index : Nat) (state after : S)
    (hr : attempt index state = ok (.retry,after)) :
    run attempt (fuel+1) index state = run attempt fuel (index+1) after := by
  simp only [run,hr,bind_tc_ok]
  rfl

theorem entropy_error {S Secret P : Type}
    (pub : ProverCommitDomain34.Source) (entropy : Entropy S Secret)
    (continuation : Secret → ProverCommitDomain34.SourceBytes → S → Result (Status P × S))
    (index : Nat) (state after : S) (error : Error)
    (he : entropy index state = ok (.Err error,after)) :
    realAttempt pub entropy continuation index state = ok (.stop error,after) := by
  simp only [realAttempt,he,bind_tc_ok]
  rfl

/-- Eight-attempt transport installs pointwise source component equalities
without deleting state, rejected effects or any suffix read before error. -/
theorem run_congr {S P : Type} (left right : Attempt S P)
    (equal : ∀ index state, left index state = right index state)
    (fuel index : Nat) (state : S) :
    run left fuel index state = run right fuel index state := by
  have eq : left = right := funext fun i => funext (equal i)
  rw [eq]

/-- The certified native walk may be installed before any publication
continuation; the entire returned oracle state is retained on both branches. -/
theorem walk_publication {S P : Type}
    (effect : Unit → ProverCommitStateLift28.Parts →
      ProverCommitStateLift28.Port S ProverCommitWalk28.Bytes32)
    (publicBytes : Slice U8) (records : ProverCommitWalk28.Records)
    (variant : transport.Variant)
    (publish : core.result.Result ProverCommitWalk28.Output Error → ProverCommitStateLift28.Port S P) :
    (ProverCommitNative30.walk effect publicBytes records variant >>= publish) =
    ((do let out ← ProverCommitInit28.walk effect publicBytes records variant
         pure out.1) >>= publish) := by
  rw [ProverCommitNative30.walk_model]

#print axioms checked_outside
#print axioms real_outside
#print axioms run_no_proof
#print axioms outside_nothing_published
#print axioms rejected_next
#print axioms entropy_error
#print axioms run_congr
#print axioms walk_publication
end R1Z.ProverCommitRetry34
