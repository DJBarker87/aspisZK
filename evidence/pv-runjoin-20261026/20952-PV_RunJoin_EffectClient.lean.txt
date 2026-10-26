import R1Z.PV_RunJoin_Source
import R1Z.ProverRwEffectOwner

/-! An effect interpretation of the selected client, with the emitted body
called literally. No pure getrandom dictionary is used for entropy. This is
interpretation syntax, not a theorem identifying native execution with it. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_EffectClient
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRwRetryModel ProverRwEffectTape ProverRwEffectSource
variable [ExternalTypes] [ExternalFuns]

structure State (N : Type) where
  entropy : World
  policy : N
  ledger : Store

/-- Extraction failures, missing replies and interpreter fuel are distinct
from the native verifier errors. None is silently made a proof or entropy error. -/
inductive Signal where
  | published : Proof → Nat → Signal
  | error : verifier.Error → Signal
  | failed : Aeneas.Std.Error → Signal
  | diverged : Signal
  | request : Slice U8 → (Reply → Result Outcome) → Signal
  | entropyFuel : Usize → Signal
  | rejected : Signal

structure Execution (N : Type) where
  state : State N
  signal : Signal

/-- The policy is invoked before entropy, exactly as in the extracted client.
Its updated state and the owner's returned world survive every returned
native entropy status, body rejection, body error, and backend failure. -/
def attempt {N : Type} (account : ProverRwEffectCallback.Account N)
    (pub : Pub) (compiled : Compiled) (hash : Hash) (index : Nat) (s : State N) : Execution N :=
  match account.call_mut s.policy (ProverCommitRetrySource34.word index) with
  | .fail e => ⟨s,.failed e⟩
  | .div => ⟨s,.diverged⟩
  | .ok (nonce,policy) =>
    let entropy := ProverRwEffectOwner.worldOwner nonce s.entropy
    let next : State N := ⟨entropy.world,policy,s.ledger⟩
    match entropy.boundary with
    | .request input resume => ⟨next,.request input resume⟩
    | .retry k => ⟨next,.entropyFuel k⟩
    | .returned (.fail e) => ⟨next,.failed e⟩
    | .returned .div => ⟨next,.diverged⟩
    | .returned (.ok (.Err _)) => ⟨next,.error .Entropy⟩
    | .returned (.ok (.Ok secret)) =>
      match prover.prove_masked_attempt pub compiled .S2 hash secret s.ledger with
      | .fail e => ⟨next,.failed e⟩
      | .div => ⟨next,.diverged⟩
      | .ok (status,ledger) =>
        let after : State N := ⟨entropy.world,policy,ledger⟩
        match status with
        | .Ok proof => ⟨after,.published proof (index+1)⟩
        | .Err .Rejected => ⟨after,.rejected⟩
        | .Err e => ⟨after,.error e⟩

/-- The only retry signal is a returned Rejected body error. The same returned
world, mutable policy and durable ledger feed the next attempt. -/
def run {N : Type} (account : ProverRwEffectCallback.Account N)
    (pub : Pub) (compiled : Compiled) (hash : Hash) : Nat → Nat → State N → Execution N
  | 0,_,s => ⟨s,.error .AttemptsExhausted⟩
  | fuel+1,index,s =>
    let out := attempt account pub compiled hash index s
    match out.signal with
    | .rejected => run account pub compiled hash fuel (index+1) out.state
    | _ => out

def client {N : Type} (account : ProverRwEffectCallback.Account N)
    (pub : Pub) (compiled : Compiled) (hash : Hash) (s : State N) : Execution N :=
  run account pub compiled hash 8 0 s

/-- The actual source entry has exactly this selected retry-owner call. This
source equation does not equate the effect interpreter with a pure dictionary. -/
theorem selected_entry {N : Type}
    (account : ProverRwEffectCallback.Account N) (pub : Pub) (compiled : Compiled)
    (hash : Hash) (store : Store) (state : N) :
    RealR1_client.prove_for_proof_accounts account pub compiled hash store state =
      prover.prove_masked_retrying_with
        (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError account)
        pub compiled .S2 hash store state :=
  PV_RunJoin_Source.proof_accounts_entry account pub compiled hash store state

#print axioms attempt
#print axioms run
#print axioms client
#print axioms selected_entry
end R1Z.PV_RunJoin_EffectClient
