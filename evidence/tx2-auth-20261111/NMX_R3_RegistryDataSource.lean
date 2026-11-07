import NMX_R3_RegistryRun
import NMX_ErrorCloneCut
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryDataSource
open Aeneas Aeneas.Std AdapterRw

def clone (aborts : Bool) (failure : Error) (e : solana_program_error.ProgramError) :
 Result solana_program_error.ProgramError :=
 if aborts && (NND_Carrier.error e).cloneAllocates then .fail failure else .ok e

def install (base : Ops) (aborts : Bool) (failure : Error) : Ops :=
 {base with op35 := clone aborts failure}

/-- Exact emitted getter at SAME account, including all String-clone results.
The standard allocation choice is independent at each reached source site. -/
theorem source (base : Ops) (env : RSL.Env) (aborts : Bool) (failure : Error)
 (a : r1_pool_adapter.owned.OwnedAccount) :
 NMX_R3_RegistryRun.command env aborts (.data a) =
 NMX_R3_RegistryRun.scalar (r1_pool_adapter.owned.OwnedAccount.data (install base aborts failure) a) := by
 cases hb : a.bytes with
 | Ok v => simp only [NMX_R3_RegistryRun.command,hb,r1_pool_adapter.owned.OwnedAccount.data,NMX_R3_RegistryRun.scalar]
 | Err e =>
  rw [NMX_ErrorCloneCut.data_error _ _ e hb]
  simp only [NMX_R3_RegistryRun.command,hb,install]
  change ((if aborts && (NND_Carrier.error e).cloneAllocates then ⟨.abort,[]⟩ else ⟨.ret (.Err e),[]⟩) :
   RSL.Obs (core.result.Result (Slice U8) solana_program_error.ProgramError)) =
   NMX_R3_RegistryRun.scalar (do let copied ← clone aborts failure e; Result.ok (core.result.Result.Err copied : core.result.Result (Slice U8) solana_program_error.ProgramError))
  unfold clone
  cases flag : (aborts && (NND_Carrier.error e).cloneAllocates) <;>
   simp only [flag,Bool.false_eq_true,↓reduceIte,bind_tc_ok,bind_tc_fail,NMX_R3_RegistryRun.scalar]
#print axioms source
end NMX_R3_RegistryDataSource
end
