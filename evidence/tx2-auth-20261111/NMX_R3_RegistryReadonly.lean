import NMX_R3_RegistryProtocols
import NMX_R3_RegistryStd
import NMX_R3_RegistryCarrier
import NND_CompareTransport
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryReadonly
open Aeneas Aeneas.Std AdapterRw NND_Carrier NMX_R3_RegistryProgram NMX_R3_RegistryEffects NMX_R3_RegistryEffectLaws
attribute [local instance] Classical.propDecidable
abbrev Output := core.result.Result Unit solana_program_error.ProgramError

def call (ops : Ops) (a : r1_pool_adapter.owned.OwnedAccount) (p : solana_pubkey.Pubkey)
 (next : Program Output) : Program Output := do
 let r ← scalar (r1_pool_adapter.owned.require_readonly_account ops a p)
 NMX_R3_RegistryProtocols.tryTail r (fun _ => next)

theorem source (ops : Ops) (a : r1_pool_adapter.owned.OwnedAccount) (p : solana_pubkey.Pubkey)
 (next : Program Output) : eval (call ops a p next) =
 RSL.Spec.bind (scalarSpec (r1_pool_adapter.owned.require_readonly_account ops a p))
  (fun r => match r with | .Ok _ => eval next | .Err e => RSL.Spec.pure (.Err e)) := by
 simp only [call,eval_bind,eval_scalar]
 apply congrArg (RSL.Spec.bind (scalarSpec (r1_pool_adapter.owned.require_readonly_account ops a p)))
 funext r
 cases r with
 | Ok u => exact NMX_R3_RegistryProtocols.eval_try (.Ok u) (fun _ => next)
 | Err e => exact NMX_R3_RegistryProtocols.eval_try (.Err e) (fun _ => next)

theorem model (a : r1_pool_adapter.owned.OwnedAccount) (p : solana_pubkey.Pubkey) :
 RSL.readonlyAccount (NMX_R3_RegistryCarrier.account a) (key p) =
 reply id (if !decide (a.owner = p) || a.is_signer || a.is_writable || a.executable
  then .Err .InvalidAccountData else .Ok ()) := by
 unfold RSL.readonlyAccount NMX_R3_RegistryCarrier.account
 simp only [NND_CompareTransport.key_ne]
 cases h : (decide (key a.owner ≠ key p) || a.is_signer || a.is_writable || a.executable) <;>
  simp only [h,Bool.false_eq_true,↓reduceIte,reply]
 <;> rfl

theorem fold (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (a : r1_pool_adapter.owned.OwnedAccount) (p : solana_pubkey.Pubkey)
 (next : Program Output) (f : RSL.RS Unit)
 (hn : RSL.Spec.map (reply id) (eval next) = f) :
 RSL.Spec.map (reply id) (eval (call (NMX_R3_RegistryOps.install base D env) a p next)) =
 RSL.RS.seq (RSL.RS.ofExcept (RSL.readonlyAccount (NMX_R3_RegistryCarrier.account a) (key p))) f := by
 rw [source,NMX_R3_RegistryStd.readonly,model]
 simp only [scalarSpec,RSL.Spec.bind_pure]
 generalize (if !decide (a.owner = p) || a.is_signer || a.is_writable || a.executable
  then core.result.Result.Err solana_program_error.ProgramError.InvalidAccountData else .Ok ()) = r
 cases r with
 | Ok u =>
  cases u
  simpa only [reply,RSL.RS.ofExcept,RSL.RS.seq,RSL.RS.bind,RSL.Spec.bind_pure] using hn
 | Err e =>
  simp only [reply,RSL.RS.ofExcept,RSL.RS.seq,RSL.RS.bind,RSL.Spec.bind_pure,NMX_R3_RegistryEffectLaws.map_pure]
  rfl
#print axioms source
#print axioms model
#print axioms fold
end NMX_R3_RegistryReadonly
end
