import NMX_R3_RegistryEffects
import NMX_R2_Observation
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryRun
open Aeneas Aeneas.Std AdapterRw NMX_R3_RegistryProgram NMX_R3_RegistryEffects

def scalar {A : Type} : Result A → RSL.Obs A
 | .ok a => ⟨.ret a,[]⟩
 | .fail _ => ⟨.abort,[]⟩
 | .div => ⟨.diverge,[]⟩

def command (env : RSL.Env) (aborts : Bool) {A : Type} : Command A → RSL.Obs A
 | .scalar r => scalar r
 | .data a => match a.bytes with
   | .Ok v => ⟨.ret (.Ok v.deref),[]⟩
   | .Err e => if aborts && (NND_Carrier.error e).cloneAllocates
       then ⟨.abort,[]⟩ else ⟨.ret (.Err e),[]⟩
 | .pda s p =>
   let reply := env.pda (s.val.map NND_Carrier.bytes) (NND_Carrier.key p)
   ⟨.ret (match reply with
     | some k => .Ok (NND_Carrier.unkey k)
     | none => .Err .InvalidSeeds),
    [.pda (s.val.map NND_Carrier.bytes) (NND_Carrier.key p) reply]⟩

/-- Each reached call has a separate allocation choice. Stops preserve only
its reached prefix; no child continuation or post-state is evaluated. -/
def run (env : RSL.Env) (allocations : Nat → Bool) {A : Type} : Program A → Nat → RSL.Obs A
 | .ret a, _ => ⟨.ret a,[]⟩
 | .call c next, n => NMX_R2_Observation.bind (command env (allocations n) c)
   (fun a => run env allocations (next a) (n+1))

theorem scalar_sound {A : Type} (r : Result A) (env : RSL.Env) :
 scalarSpec r env (scalar r) := by cases r <;> rfl

theorem allocation_sound {A : Type} (a : A) (env : RSL.Env) (flag aborts : Bool) :
 RSL.Spec.bind (RSL.Spec.allocIf flag) (fun _ => RSL.Spec.pure a) env
  (if aborts && flag then ⟨.abort,[]⟩ else ⟨.ret a,[]⟩) := by
 cases flag <;> cases aborts
 · exact Or.inl ⟨(),[],⟨.ret a,[]⟩,rfl,rfl,rfl⟩
 · exact Or.inl ⟨(),[],⟨.ret a,[]⟩,rfl,rfl,rfl⟩
 · exact Or.inl ⟨(),[],⟨.ret a,[]⟩,Or.inl rfl,rfl,rfl⟩
 · exact Or.inr (Or.inl ⟨[],Or.inr rfl,rfl⟩)

theorem data_sound (a : r1_pool_adapter.owned.OwnedAccount) (env : RSL.Env) (aborts : Bool) :
 dataSpec a env (command env aborts (.data a)) := by
 cases h : a.bytes with
 | Ok v => simp only [dataSpec,command,h]; rfl
 | Err e =>
  simp only [dataSpec,command,h]
  exact allocation_sound (core.result.Result.Err e : core.result.Result (Slice U8) solana_program_error.ProgramError) env (NND_Carrier.error e).cloneAllocates aborts

theorem pda_sound (s : Slice (Slice U8)) (p : solana_pubkey.Pubkey)
 (env : RSL.Env) (aborts : Bool) :
 pdaSpec s p env (command env aborts (.pda s p)) := by
 let seeds := s.val.map NND_Carrier.bytes
 let program := NND_Carrier.key p
 let reply := env.pda seeds program
 exact Or.inl ⟨reply,[.pda seeds program reply],_,
  Or.inl ⟨reply,[],_,rfl,
   Or.inl ⟨(),[.pda seeds program reply],_,rfl,rfl,rfl⟩,rfl⟩,rfl,rfl⟩

theorem command_sound (env : RSL.Env) (aborts : Bool) {A : Type} (c : Command A) :
 commandSpec c env (command env aborts c) := by
 cases c with
 | scalar r => exact scalar_sound r env
 | data a => exact data_sound a env aborts
 | pda s p => exact pda_sound s p env aborts

theorem sound (env : RSL.Env) (allocations : Nat → Bool) {A : Type}
 (p : Program A) (n : Nat) : eval p env (run env allocations p n) := by
 induction p generalizing n with
 | ret a => rfl
 | call c next ih =>
  exact NMX_R2_Observation.bind_sound _ _ _ _ env
   (command_sound env (allocations n) c) (fun a => ih a (n+1))

#print axioms scalar_sound
#print axioms allocation_sound
#print axioms data_sound
#print axioms pda_sound
#print axioms command_sound
#print axioms sound
end NMX_R3_RegistryRun
end
