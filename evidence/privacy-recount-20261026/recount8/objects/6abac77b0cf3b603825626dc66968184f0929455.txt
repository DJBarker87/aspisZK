import R1Z.PV_RunJoin_EffectReplay
import R1Z.ProverRwEffectOwner
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_EffectInventory
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRwRetryModel (Pub Compiled Hash)
open ProverRwEffectTape (World)
open PV_RunJoin_EffectClient
variable [ExternalTypes] [ExternalFuns]

/-- Conservation is about the full served replies, including the draw that
caused an error. It does not identify replies with an OS probability law. -/
def contents (s : World) := s.reads.map Prod.snd ++ s.tape

theorem attempt_contents {N : Type} (account : ProverRwEffectCallback.Account N)
    (pub : Pub) (compiled : Compiled) (hash : Hash) (index : Nat) (s : State N) :
    contents (attempt account pub compiled hash index s).state.entropy = contents s.entropy := by
  unfold attempt
  cases hp : account.call_mut s.policy (ProverCommitRetrySource34.word index) with
  | fail e => rfl
  | div => rfl
  | ok pair =>
    rcases pair with ⟨nonce,next⟩
    dsimp only
    have inv := ProverRwEffectOwner.owner_tape nonce s.entropy
    generalize he : ProverRwEffectOwner.worldOwner nonce s.entropy = entropy at *
    rcases entropy with ⟨boundary,world⟩
    change contents world = contents s.entropy at inv
    cases boundary with
    | request input resume => exact inv
    | retry k => exact inv
    | returned status =>
      cases status with
      | fail e => exact inv
      | div => exact inv
      | ok status =>
        cases status with
        | Err e => exact inv
        | Ok secret =>
          dsimp only
          cases hb : prover.prove_masked_attempt pub compiled .S2 hash secret s.ledger with
          | fail e => exact inv
          | div => exact inv
          | ok pair =>
            rcases pair with ⟨status,ledger⟩
            cases status with
            | Ok proof => exact inv
            | Err e => cases e <;> exact inv

theorem run_contents {N : Type} (account : ProverRwEffectCallback.Account N)
    (pub : Pub) (compiled : Compiled) (hash : Hash) (fuel index : Nat) (s : State N) :
    contents (run account pub compiled hash fuel index s).state.entropy = contents s.entropy := by
  induction fuel generalizing index s with
  | zero => rfl
  | succ fuel ih =>
    have inv := attempt_contents account pub compiled hash index s
    simp only [run]
    split
    · exact (ih _ _).trans inv
    · exact inv

theorem client_contents {N : Type} (account : ProverRwEffectCallback.Account N)
    (pub : Pub) (compiled : Compiled) (hash : Hash) (s : State N) :
    contents (client account pub compiled hash s).state.entropy = contents s.entropy :=
  run_contents account pub compiled hash 8 0 s

#print axioms contents
#print axioms attempt_contents
#print axioms run_contents
#print axioms client_contents
end R1Z.PV_RunJoin_EffectInventory
