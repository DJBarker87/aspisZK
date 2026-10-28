import R1Z.ProverRwEffectOwner
import R1Z.ProverRwRetryModel

/-! Checked factoring of the actual proof-account callback at its entropy-owner
call. The source account-key callback remains ordered before entropy. -/
set_option autoImplicit false
namespace R1Z.ProverRwEffectCallback
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRwEffectSource ProverRwEffectOwner
variable [ExternalTypes] [ExternalFuns]
abbrev Account (C : Type) := core.ops.function.FnMut C Usize (Array U8 32#usize)
abbrev SourceCall {C : Type} := RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError.call_mut (T0 := C)

def callback {C : Type} (account : Account C) (generate : Array U8 32#usize → Result Status)
    (state : RealR1_client.prove_for_proof_accounts.closure C) (k : Usize) := do
  let (nonce,afterAccount) ← account.call_mut state k
  let entropy ← generate nonce
  let mapped ← core.result.Result.map_err
    (RealR1_client.prove_for_proof_accounts.closure.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyAttemptEntropyErrorError account)
    entropy ()
  .ok (mapped,afterAccount,fun c : RealR1_client.prove_for_proof_accounts.closure C => c)

theorem callback_eq {C : Type} (account : Account C)
    (state : RealR1_client.prove_for_proof_accounts.closure C) (k : Usize) :
    callback account pureOwner state k = SourceCall account state k := by
  simp only [callback,SourceCall,
    RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError.call_mut,
    pure_owner_eq]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro value called
  rcases value with ⟨nonce,next⟩
  rfl

/-- Replacing the entropy owner by its checked pure factoring leaves the actual
callback's FnMut interface unchanged, including its updated account state and
backwards continuation. This installs no arbitrary-world native dictionary. -/
theorem callback_dictionary_eq {C : Type} (account : Account C) :
    (fun state k => callback account pureOwner state k) =
      (fun state k => SourceCall account state k) := by
  funext state k
  exact callback_eq account state k

#print axioms callback_eq
#print axioms callback_dictionary_eq
end R1Z.ProverRwEffectCallback
