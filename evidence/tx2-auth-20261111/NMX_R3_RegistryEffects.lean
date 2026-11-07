import NMX_R3_RegistryProgram
import NMX_R2_SpecAssociativity
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryEffects
open Aeneas Aeneas.Std AdapterRw NMX_R3_RegistryProgram

def scalarSpec {A : Type} : Result A → RSL.Spec A
 | .ok a => RSL.Spec.pure a
 | .fail _ => RSL.Spec.panic
 | .div => fun _ o => o = ⟨.diverge,[]⟩

/-- The clone allocation is reached only on a heap-carrying deferred error.
No post-abort account state is part of this observation. -/
def dataSpec (a : r1_pool_adapter.owned.OwnedAccount) :
 RSL.Spec (core.result.Result (Slice U8) solana_program_error.ProgramError) :=
 match a.bytes with
 | .Ok v => RSL.Spec.pure (.Ok v.deref)
 | .Err e => RSL.Spec.bind (RSL.Spec.allocIf (NND_Carrier.error e).cloneAllocates)
   (fun _ => RSL.Spec.pure (.Err e))

def pdaSpec (s : Slice (Slice U8)) (p : solana_pubkey.Pubkey) :
 RSL.Spec (core.result.Result solana_pubkey.Pubkey solana_pubkey.PubkeyError) :=
 RSL.Spec.map (fun r => match r with
   | some k => .Ok (NND_Carrier.unkey k)
   | none => .Err .InvalidSeeds)
  (RSL.pdaCall (s.val.map NND_Carrier.bytes) (NND_Carrier.key p))

def commandSpec {A : Type} : Command A → RSL.Spec A
 | .scalar r => scalarSpec r
 | .data a => dataSpec a
 | .pda s p => pdaSpec s p

def eval {A : Type} : Program A → RSL.Spec A
 | .ret a => RSL.Spec.pure a
 | .call c next => RSL.Spec.bind (commandSpec c) (fun a => eval (next a))

theorem eval_bind {A B : Type} (p : Program A) (k : A → Program B) :
 eval (p >>= k) = RSL.Spec.bind (eval p) (fun a => eval (k a)) := by
 induction p with
 | ret a =>
  change eval (k a) = RSL.Spec.bind (RSL.Spec.pure a) (fun a => eval (k a))
  exact (RSL.Spec.bind_pure a (fun a => eval (k a))).symm
 | call c next ih =>
  change RSL.Spec.bind (commandSpec c) (fun a => eval (NMX_R3_RegistryProgram.bind (next a) k)) =
   RSL.Spec.bind (RSL.Spec.bind (commandSpec c) (fun a => eval (next a)))
    (fun a => eval (k a))
  rw [NMX_R2_SpecAssociativity.bind]
  apply congrArg (RSL.Spec.bind (commandSpec c))
  funext a
  exact ih a

#print axioms eval_bind
end NMX_R3_RegistryEffects
end
