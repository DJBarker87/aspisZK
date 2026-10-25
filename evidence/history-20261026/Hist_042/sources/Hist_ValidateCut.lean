import S2X_SecondCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_ValidateCut
open Aeneas Aeneas.Std Result
open AspisR1.AdapterRw.Cuts
attribute [local irreducible]
  AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts
  AdapterRw.r1_pool_adapter.owned.OwnedAccount.data

/-- Successful validation exposes the actual successful authenticated-account
call, rather than assuming authentication of a separately selected snapshot. -/
theorem authenticated (ops : AdapterRw.Ops) (verifier : AdapterRw.solana_pubkey.Pubkey)
    (accounts : Slice Account) (data : Slice U8) (current : core.result.Result U64 PE)
    (out : AdapterRw.r1_pool_adapter.ValidatedAsqa)
    (accepted : AdapterRw.r1_pool_adapter.owned.validate_asq8 ops verifier accounts data current = ok (.Ok out)) :
    ∃ pool lane slot authenticated,
      AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts ops verifier accounts pool lane slot = ok (.Ok authenticated) := by
  unfold AdapterRw.r1_pool_adapter.owned.validate_asq8 at accepted
  simp only [AdapterRw.core.result.Result.map_err] at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals try simp only [error_bind_ne_ok] at *
  all_goals aesop (add simp [bne_iff_ne])

#print axioms authenticated
end AspisR1.Hist_ValidateCut
end
