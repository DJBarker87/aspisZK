import AdapterRwCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCK_ScanDependency
open Aeneas Aeneas.Std Result
open AdapterRw.Cuts
attribute [local irreducible] _root_.AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts
  _root_.AdapterRw.r1_pool_adapter.owned.OwnedAccount.data
/-- Exact missing op51 postcondition, separate from U16 acceptance.
This is not asserted as a native theorem by this module. -/
def ScannerLength (ops : _root_.AdapterRw.Ops) : Prop :=
  ∀ (raw : Slice U8) (scan : _root_.AdapterRw.r1_pool_adapter.ScannedAsqaProof),
    ops.op51 raw = ok (.Ok scan) → scan.proof_length = 57607#usize

theorem validated_length (ops : _root_.AdapterRw.Ops)
    (program : _root_.AdapterRw.solana_pubkey.Pubkey) (accounts : Slice Account)
    (data : Slice U8) (slot : core.result.Result U64 PE)
    (validated : _root_.AdapterRw.r1_pool_adapter.ValidatedAsqa)
    (scanner : ScannerLength ops)
    (accepted : _root_.AdapterRw.r1_pool_adapter.owned.validate_asq8 ops
      program accounts data slot = ok (.Ok validated)) :
    validated.proof_length = 57607#usize := by
  unfold _root_.AdapterRw.r1_pool_adapter.owned.validate_asq8 at accepted
  simp only [_root_.AdapterRw.core.result.Result.map_err] at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals try simp only [error_bind_ne_ok] at *
  all_goals
    have same := core.result.Result.Ok.inj (Result.ok.inj accepted)
    rw [←same]
    exact scanner _ _ (by assumption)
#print axioms validated_length
end AspisR1.NCK_ScanDependency
end
