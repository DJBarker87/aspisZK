import NCK_AuthenticationCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCK_ValidatedAuthCall
open Aeneas Aeneas.Std Result
open AdapterRw.Cuts
open _root_.AdapterRw.r1_pool_adapter.owned
attribute [local irreducible] authenticate_asq8_accounts OwnedAccount.data
/-- ASQ8 validation acceptance derives its actual authentication child and
successful slot on the SAME account slice. No independent child run enters. -/
theorem source (ops : _root_.AdapterRw.Ops)
    (program : _root_.AdapterRw.solana_pubkey.Pubkey) (accounts : Slice Account)
    (data : Slice U8) (slot : core.result.Result U64 PE)
    (validated : _root_.AdapterRw.r1_pool_adapter.ValidatedAsqa)
    (success : validate_asq8 ops program accounts data slot = ok (.Ok validated)) :
    ∃ pool : _root_.AdapterRw.solana_pubkey.Pubkey, ∃ lane current authenticated,
      slot = .Ok current ∧
      authenticate_asq8_accounts ops program accounts pool lane current = ok (.Ok authenticated) := by
  unfold validate_asq8 at success
  simp only [_root_.AdapterRw.core.result.Result.map_err] at success
  repeat' first
  | (solve | cases success)
  | uncase_result
  | head_reduce success
  | split at success
  all_goals exact ⟨_,_,_,_,rfl,by assumption⟩
#print axioms source
end AspisR1.NCK_ValidatedAuthCall
end
