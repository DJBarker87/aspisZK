import Hiq_PoolSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_PoolGuards
open Aeneas Aeneas.Std Result Hiq_PoolSource

theorem account_iff (a : AdapterRw.Cuts.Account) (id : AdapterRw.solana_pubkey.Pubkey) (writable : Bool) :
    history.require_program_account a id writable = ok (.Ok ()) ↔
      a.owner = id ∧ a.executable = false ∧ a.is_writable = writable := by
  classical
  unfold history.require_program_account keyNe Hist_Authority.keyEq
  by_cases owner : a.owner = id
  · simp only [owner,decide_true,bind_tc_ok,Bool.not_true,if_false]
    cases h : a.executable <;> cases w : a.is_writable <;> cases writable <;> simp [h,w]
  · simp [owner]

theorem owned_iff (a : AdapterRw.Cuts.Account) (id : AdapterRw.solana_pubkey.Pubkey) :
    history.require_program_owned a id = ok (.Ok ()) ↔ a.owner = id ∧ a.executable = false := by
  classical
  unfold history.require_program_owned keyNe Hist_Authority.keyEq
  by_cases owner : a.owner = id
  · simp only [owner,decide_true,bind_tc_ok,Bool.not_true,if_false]
    cases h : a.executable <;> simp [h]
  · simp [owner]

#print axioms account_iff
#print axioms owned_iff
end AspisR1.Hiq_PoolGuards
end
