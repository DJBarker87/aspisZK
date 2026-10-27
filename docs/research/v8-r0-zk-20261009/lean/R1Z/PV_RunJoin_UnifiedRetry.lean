import R1Z.PV_RunJoin_SourceBinding
import R1Z.ProverRwEffectCallback
import R1Z.ProverCommitRetry34
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_UnifiedRetry
open Aeneas Aeneas.Std Result
open ProverRwRngCaller
open R1Z.ProverRwRetryModel (Proof Secret)
variable [ProverRwFull.ExternalTypes] [NativeTypes] [ErasureFns]

/-- ONE changing world: body effects can update the very public context read
by the next nonce policy. Separately threading an opaque store handle would
not establish this sharing with its backing filesystem or oracle context. -/
structure State (N L C : Type) where
  provider : Tape
  policy : N
  ledger : L
  client : C

abbrev Body (S : Type) := Secret → S → Result (core.result.Result Proof ProverRwFull.verifier.Error × S)

/-- The actual selected callback order, interpreted with explicit state. The
account closure receives the whole current world. The native owner retains
the provider on OS errors and on rejected draws. -/
def entropy {N L C : Type}
    (account : R1Z.ProverRwEffectCallback.Account (State N L C))
    (index : Nat) (s : State N L C) :
    Result (core.result.Result Secret ProverRwFull.verifier.Error × State N L C) := do
  let (nonce,next) ← account.call_mut s (ProverCommitRetrySource34.word index)
  let (provider,status) ← StateOnlyAttemptSecrets.generate_with
    Tape.Insts.Prover_rw_rng_callerDraw64 nonce next.provider
  let final := {next with provider := provider}
  match status with
  | .Err _ => .ok (.Err .Entropy,final)
  | .Ok secret => .ok (.Ok (PV_RunJoin_SourceBinding.secret secret),final)

def attempt {N L C : Type}
    (account : R1Z.ProverRwEffectCallback.Account (State N L C)) (body : Body (State N L C)) :
    ProverCommitRetry34.Attempt (State N L C) Proof := fun index s => do
  let (status,next) ← entropy account index s
  match status with
  | .Err e => .ok (.stop (ProverRwRetryModel.error e),next)
  | .Ok secret =>
    let (result,final) ← body secret next
    match result with
    | .Ok proof => .ok (.done proof,final)
    | .Err .Rejected => .ok (.retry,final)
    | .Err e => .ok (.stop (ProverRwRetryModel.error e),final)

def client {N L C : Type}
    (account : R1Z.ProverRwEffectCallback.Account (State N L C))
    (body : Body (State N L C)) (s : State N L C) :=
  ProverCommitRetry34.eight (attempt account body) s

/-- Full emitted source body boundary. Native ledger/oracle effects in the
returned world are separately associated; no pure entropy entry is installed. -/
structure SourceBody (S : Type) where
  ops : S → ProverRwFull.ExternalFuns
  pub : S → ProverRwRetryModel.Pub
  compiled : S → ProverRwRetryModel.Compiled
  hash : S → ProverRwRetryModel.Hash
  store : S → ProverRwRetryModel.Store

def BodySourceLaw {S : Type} (d : SourceBody S) (body : Body S) : Prop :=
  ∀ s secret,
    ProverCommitSemanticTransport26.mapR (fun out => (out.1,d.store out.2)) (body secret s) =
      letI : ProverRwFull.ExternalFuns := d.ops s
      ProverRwFull.prover.prove_masked_attempt (d.pub s) (d.compiled s) .S2 (d.hash s) secret (d.store s)

#print axioms entropy
#print axioms attempt
#print axioms client
#print axioms BodySourceLaw
end R1Z.PV_RunJoin_UnifiedRetry
