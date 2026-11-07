import NND_RegistryStd
import NND_ResultTotal
import NGL_ArrayEquality
set_option autoImplicit false
noncomputable section
namespace NND_RegistryTotalPrimitives
open Aeneas Aeneas.Std Result AdapterRw NND_ResultTotal

theorem data (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (a : r1_pool_adapter.owned.OwnedAccount) :
 Total (r1_pool_adapter.owned.OwnedAccount.data (NND_RegistryOps.install base D env) a) := by
 rw [NND_RegistryStd.data]
 exact pure _

theorem readonly (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (a : r1_pool_adapter.owned.OwnedAccount) (p : solana_pubkey.Pubkey) :
 Total (r1_pool_adapter.owned.require_readonly_account (NND_RegistryOps.install base D env) a p) := by
 rw [NND_RegistryStd.readonly]
 exact pure _

theorem key_ne (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (p q : solana_pubkey.Pubkey) :
 Total (core.cmp.impls.PartialEqShared.ne
  (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey (NND_RegistryOps.install base D env)) p q) := by
 rw [NND_RegistryStd.key_ne]
 exact pure _

theorem array_ne {N : Usize} (p q : Array U8 N) :
 Total (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 p q) := by
 rw [NGL_ArrayEquality.ne_value]
 exact pure _

theorem try_branch {A E : Type} (r : core.result.Result A E) :
 Total (core.result.Result.Insts.CoreOpsTry.branch r) := by
 cases r <;> exact pure _

theorem map_error {A E F O : Type} (inst : core.ops.function.FnOnce O E F)
 (r : core.result.Result A E) (op : O) (h : ∀ e, Total (inst.call_once op e)) :
 Total (core.result.Result.map_err inst r op) := by
 cases r with
 | Ok a => exact pure _
 | Err e => exact bind _ _ (h e) (fun _ => pure _)

#print axioms data
#print axioms readonly
#print axioms key_ne
#print axioms array_ne
#print axioms try_branch
#print axioms map_error
end NND_RegistryTotalPrimitives
end
