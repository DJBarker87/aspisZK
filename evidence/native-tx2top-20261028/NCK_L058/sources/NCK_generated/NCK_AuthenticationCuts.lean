import NCK_Distinct
import NCK_Owners
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCK_AuthenticationCuts
open Aeneas Aeneas.Std Result
open AdapterRw.Cuts
open _root_.AdapterRw.r1_pool_adapter.owned
attribute [local irreducible] require_readonly_buffer require_readonly_account
  require_verifier_checkpoint require_distinct_accounts OwnedAccount.data
  authenticate_invariant_release_registry

elab "NCK_uncase_unit" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun goal => goal.withContext do
    for decl in ← Lean.getLCtx do
      let type ← Lean.Meta.whnf decl.type
      if type.isConstOf ``Unit then
        return (← goal.cases decl.fvarId).toList.map (·.mvarId)
    throwError "no unit variable"

/-- Every guard below belongs to the SAME accepted authentication invocation.
Decoder/PDA/reconstruction results are not assumed successful independently. -/
theorem guards (ops : _root_.AdapterRw.Ops)
    (program pool : _root_.AdapterRw.solana_pubkey.Pubkey) (accounts : Slice Account)
    (lane : U8) (slot : U64)
    (authenticated : _root_.AdapterRw.r1_pool_adapter.AuthenticatedAsq8Accounts)
    (success : authenticate_asq8_accounts ops program accounts pool lane slot = ok (.Ok authenticated)) :
    ∃ proof master poolCheckpoint laneAccount registry entry checkpoint,
      Slice.len accounts = 7#usize ∧
      Slice.index_usize accounts 0#usize = ok proof ∧
      Slice.index_usize accounts 1#usize = ok master ∧
      Slice.index_usize accounts 2#usize = ok poolCheckpoint ∧
      Slice.index_usize accounts 3#usize = ok laneAccount ∧
      Slice.index_usize accounts 4#usize = ok registry ∧
      Slice.index_usize accounts 5#usize = ok entry ∧
      Slice.index_usize accounts 6#usize = ok checkpoint ∧
      require_readonly_buffer proof = ok (.Ok ()) ∧
      require_verifier_checkpoint ops checkpoint program false = ok (.Ok ()) ∧
      require_readonly_account ops master pool = ok (.Ok ()) ∧
      require_readonly_account ops poolCheckpoint pool = ok (.Ok ()) ∧
      require_readonly_account ops laneAccount pool = ok (.Ok ()) ∧
      require_distinct_accounts ops (Array.make 7#usize
        [proof,master,poolCheckpoint,laneAccount,registry,entry,checkpoint]) = ok (.Ok ()) := by
  unfold authenticate_asq8_accounts at success
  repeat' first
  | (solve | exact ⟨_,_,_,_,_,_,_,by assumption,by assumption,by assumption,
      by assumption,by assumption,by assumption,by assumption,by assumption,
      by assumption,by assumption,by assumption,by assumption,by assumption,by assumption⟩)
  | NCK_uncase_unit
  | (solve | cases success)
  | uncase_result
  | head_reduce success
  | split at success
  all_goals trace_state
#print axioms guards
end AspisR1.NCK_AuthenticationCuts
end
