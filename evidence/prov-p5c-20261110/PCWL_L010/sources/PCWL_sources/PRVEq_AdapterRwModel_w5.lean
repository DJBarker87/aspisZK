-- PCWL_ AdapterRwModel, Ops-parametric items (readonly_meta_ok, require_readonly_account). Statements: fresh = gate.
-- Fresh text: PCWL_E001 emission (Charon cargo --jobs 4 identity by class receipt PCWE_E003; original Aeneas 959659a6; overflow ON; frozen 4bb3b3f), blocks readonly_meta_ok,
-- OwnedAccount.impl.owner, require_readonly_account. The emission's one external (Pubkey eq; an axiom in FunsExternal) is the field pk_eq of the parameter Ext, not an axiom.
-- RESULT CLASS: CONDITIONAL_ON_BINDING. The gate takes `ops : Ops` and uses ops.op38 as Pubkey equality; the equalities hold for every Ext whose pk_eq is bound to ops.op38.
-- Callees outside the list (core.cmp.impls.PartialEqShared.ne, trait_default, ProgramError, OwnedAccount fields) resolve by name to the gate's declarations.
import Aeneas
import AdapterRwModel
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace AdapterRw
namespace PRVFresh_ARM_w5

structure Ext where
  pk_eq : solana_pubkey.Pubkey → solana_pubkey.Pubkey → Result Bool

@[reducible]
impl_def solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey (x : Ext) : core.cmp.PartialEq
  solana_pubkey.Pubkey solana_pubkey.Pubkey := {
  eq := x.pk_eq
  ne := core.cmp.PartialEq.ne.trait_default
    (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey x)
}

/-- [aspis_r1_cost_probe_program::r1_pool_adapter::readonly_meta_ok]:
    Source: 'programs/r1-cost-probe/src/r1_pool_adapter.rs', lines 170:0-181:1 -/
def r1_pool_adapter.readonly_meta_ok (x : Ext)
  (owner : solana_pubkey.Pubkey) (expected : solana_pubkey.Pubkey)
  (is_signer : Bool) (is_writable : Bool) (executable : Bool) :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  let b ←
    core.cmp.impls.PartialEqShared.ne
      (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey x) owner expected
  if b
  then
    ok (core.result.Result.Err
      solana_program_error.ProgramError.InvalidAccountData)
  else
    if is_signer
    then
      ok (core.result.Result.Err
        solana_program_error.ProgramError.InvalidAccountData)
    else
      if is_writable
      then
        ok (core.result.Result.Err
          solana_program_error.ProgramError.InvalidAccountData)
      else
        if executable
        then
          ok (core.result.Result.Err
            solana_program_error.ProgramError.InvalidAccountData)
        else ok (core.result.Result.Ok ())

/-- [aspis_r1_cost_probe_program::r1_pool_adapter::owned::{aspis_r1_cost_probe_program::r1_pool_adapter::owned::OwnedAccount}::owner]:
    Source: 'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs', lines 20:4-20:46 -/
def r1_pool_adapter.owned.OwnedAccount.impl.owner
  (self : r1_pool_adapter.owned.OwnedAccount) :
  Result solana_pubkey.Pubkey
  := do
  ok self.owner

/-- [aspis_r1_cost_probe_program::r1_pool_adapter::owned::require_readonly_account]:
    Source: 'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs', lines 48:0-50:1 -/
def r1_pool_adapter.owned.require_readonly_account (x : Ext)
  (account : r1_pool_adapter.owned.OwnedAccount) (owner : solana_pubkey.Pubkey)
  :
  Result (core.result.Result Unit solana_program_error.ProgramError)
  := do
  let p ← r1_pool_adapter.owned.OwnedAccount.impl.owner account
  (r1_pool_adapter.readonly_meta_ok x) p owner account.is_signer
    account.is_writable account.executable

end PRVFresh_ARM_w5
end AdapterRw

set_option maxHeartbeats 200000

namespace PRVEq.AdapterRwModel_w5
open AdapterRw

set_option maxHeartbeats 200000 in
theorem readonly_meta_ok_eq (ops : Ops) (x : PRVFresh_ARM_w5.Ext) (h : x.pk_eq = ops.op38) :
    PRVFresh_ARM_w5.r1_pool_adapter.readonly_meta_ok x = AdapterRw.r1_pool_adapter.readonly_meta_ok ops := by
  cases x; simp only at h; subst h; rfl
#print axioms readonly_meta_ok_eq

set_option maxHeartbeats 200000 in
theorem owner_eq : @PRVFresh_ARM_w5.r1_pool_adapter.owned.OwnedAccount.impl.owner = @AdapterRw.r1_pool_adapter.owned.OwnedAccount.impl.owner := by
  rfl
#print axioms owner_eq

set_option maxHeartbeats 200000 in
theorem require_readonly_account_eq (ops : Ops) (x : PRVFresh_ARM_w5.Ext) (h : x.pk_eq = ops.op38) :
    PRVFresh_ARM_w5.r1_pool_adapter.owned.require_readonly_account x = AdapterRw.r1_pool_adapter.owned.require_readonly_account ops := by
  cases x; simp only at h; subst h; rfl
#print axioms require_readonly_account_eq

end PRVEq.AdapterRwModel_w5
