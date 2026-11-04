import PV_STX_Entropy
import PV_STX_Map
set_option autoImplicit false
noncomputable section
namespace PV_STX_Account
open Aeneas Aeneas.Std ProverRwFull PV_STX_Code PV_STX_DenoteRules
variable [ExternalTypes] [ExternalFuns]
abbrev Secrets := aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
abbrev EntropyError := aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError
abbrev AccountInst (T : Type) := core.ops.function.FnMut T Usize (Array U8 32#usize)

/-- Original generic FnMut invocation is an external-call point, with its
actual receiver/capture and index. Entropy requests share the same machine. -/
inductive Request : Type → Type 1 where
  | account {T : Type} (inst : AccountInst T) (capture : T) (index : Usize) :
      Request ((Array U8 32#usize) × T)
  | mapError {T : Type} (inst : AccountInst T)
      (r : core.result.Result Secrets EntropyError) : Request (core.result.Result Secrets verifier.Error)
  | entropy {X : Type} (request : PV_STX_Entropy.Request X) : Request X

def fixed : {X : Type} → Request X → Result X
  | _, .account inst c i => inst.call_mut c i
  | _, .mapError inst r => core.result.Result.map_err
      (RealR1_client.prove_for_proof_accounts.closure.closure.Insts.CoreOpsFunctionFnOnceTupleStateOnlyAttemptEntropyErrorError inst) r ()
  | _, .entropy op => PV_STX_Entropy.fixed op

def callMut {T : Type} (inst : AccountInst T) (capture : T) (i : Usize) :
    Code Request ((core.result.Result Secrets verifier.Error) × T × (T → T)) := do
  let (a,t) ← Code.call (Request.account inst capture i)
  let r ← PV_STX_Map.map (fun op => Request.entropy op) (PV_STX_Entropy.generate a)
  let r1 ← Code.call (Request.mapError inst r)
  pure (r1,t,fun c => c)

def next {T : Type} (inst : AccountInst T) (capture : T) (i : Usize) :
    Code Request ((core.result.Result Secrets verifier.Error) × T) := do
  let (r,c,back) ← callMut inst capture i
  pure (r,back c)

theorem entropy_erases (nonce : Array U8 32#usize) :
    denote fixed (PV_STX_Map.map (fun op => Request.entropy op) (PV_STX_Entropy.generate nonce)) =
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce nonce := by
  rw [PV_STX_Map.denote_map (fun op => Request.entropy op) PV_STX_Entropy.fixed fixed (fun _ => rfl)]
  exact PV_STX_Entropy.generate_erases nonce

theorem callMut_erases {T : Type} (inst : AccountInst T) (capture : T) (i : Usize) :
    denote fixed (callMut inst capture i) =
      RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError.call_mut inst capture i := by
  simp only [callMut,bind_rule,call_rule,pure_rule,entropy_erases,fixed,
    RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError.call_mut]
  simp only [Bind.bind,Aeneas.Std.bind]
  repeat first | rfl | split

theorem next_erases {T : Type} (inst : AccountInst T) (capture : T) (i : Usize) :
    denote fixed (next inst capture i) =
      (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError inst).call_mut capture i := by
  simp only [next,bind_rule,callMut_erases,pure_rule,
    RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError]
  simp only [Bind.bind,Aeneas.Std.bind]
  repeat first | rfl | split

#print axioms entropy_erases
#print axioms callMut_erases
#print axioms next_erases
end PV_STX_Account
