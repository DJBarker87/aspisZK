import NCK_Stage2Shape
import AdapterRwCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCK_Admission
open Aeneas Aeneas.Std Result
open AdapterRw.Cuts
attribute [local irreducible] _root_.AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts
  _root_.AdapterRw.r1_pool_adapter.owned.OwnedAccount.data
/-- Account arity is derived before the owned body can accept. -/
theorem seven_accounts (ops : _root_.AdapterRw.Ops)
    (program : _root_.AdapterRw.solana_pubkey.Pubkey) (accounts : Slice Account)
    (data : Slice U8) (slot : core.result.Result U64 PE)
    (accepted : _root_.AdapterRw.r1_pool_adapter.owned.stage2_owned ops
      program accounts data slot = ok (.Ok ())) :
    Slice.len accounts = 7#usize := by
  unfold _root_.AdapterRw.r1_pool_adapter.owned.stage2_owned at accepted
  head_reduce accepted
  split at accepted
  · cases accepted
  · rename_i within
    simpa only [bne_iff_ne, not_not] using within
/-- A deferred Clock error cannot be converted to success by an arbitrary
callee operation dictionary. The runtime Clock law itself remains separate. -/
theorem clock_success (ops : _root_.AdapterRw.Ops)
    (program : _root_.AdapterRw.solana_pubkey.Pubkey) (accounts : Slice Account)
    (data : Slice U8) (slot : core.result.Result U64 PE)
    (validated : _root_.AdapterRw.r1_pool_adapter.ValidatedAsqa)
    (accepted : _root_.AdapterRw.r1_pool_adapter.owned.validate_asq8 ops
      program accounts data slot = ok (.Ok validated)) :
    ∃ current : U64, slot = .Ok current := by
  unfold _root_.AdapterRw.r1_pool_adapter.owned.validate_asq8 at accepted
  simp only [_root_.AdapterRw.core.result.Result.map_err] at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals try simp only [error_bind_ne_ok] at *
  all_goals exact ⟨_,rfl⟩
#print axioms seven_accounts
#print axioms clock_success
end AspisR1.NCK_Admission
end
