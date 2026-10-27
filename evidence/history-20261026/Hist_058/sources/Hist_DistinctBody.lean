import Hist_Authority
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_DistinctBody
open Aeneas Aeneas.Std Result ControlFlow
abbrev Account := AdapterRw.Cuts.Account
abbrev PE := AdapterRw.Cuts.PE
local instance : DecidableEq AdapterRw.solana_pubkey.Pubkey := Classical.decEq _

theorem successor (previous index : Usize) (ordered : previous < index) :
    (Usize.wrapping_add previous 1#usize).val = previous.val+1 := by
  rw [Usize.wrapping_add_val_eq]
  change (previous.val + 1) % UScalar.size .Usize = previous.val+1
  apply Nat.mod_eq_of_lt
  apply lt_of_le_of_lt (show previous.val+1 ≤ index.val from by scalar_tac)
  exact index.bv.isLt

theorem array_read {N : Usize} (accounts : Array Account N) (index : Usize)
    (bound : index < N) :
    Array.index_usize accounts index = ok (accounts.val[index.val]'(by rw [accounts.property]; scalar_tac)) := by
  obtain ⟨value,read,same⟩ := WP.spec_imp_exists (Array.index_usize_spec accounts index (by change index.val < accounts.val.length; rw [accounts.property]; scalar_tac))
  simpa only [same] using read

/-- One literal source comparison. This separates the small symbolic loop
invariant from any concrete seven-account normalization. -/
theorem body {N : Usize} (base : AdapterRw.Ops) (accounts : Array Account N)
    (index previous : Usize) (bound : index < N) (ordered : previous < index) :
    AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body
      (Hist_Authority.install base) accounts index previous =
      if (accounts.val[previous.val]'(by rw [accounts.property]; scalar_tac)).key =
        (accounts.val[index.val]'(by rw [accounts.property]; scalar_tac)).key
      then ok (done (some (.Err AdapterRw.solana_program_error.ProgramError.InvalidArgument)))
      else ok (cont (Usize.wrapping_add previous 1#usize)) := by
  have before : previous < N := by scalar_tac
  rw [AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body,if_pos ordered,
    array_read accounts previous before,bind_tc_ok,
    AdapterRw.r1_pool_adapter.owned.OwnedAccount.impl.key,bind_tc_ok,
    array_read accounts index bound,bind_tc_ok,
    AdapterRw.r1_pool_adapter.owned.OwnedAccount.impl.key,bind_tc_ok]
  simp only [Hist_Authority.install,Hist_Authority.keyEq,bind_tc_ok]
  split <;> simp_all [lift]

#print axioms successor
#print axioms array_read
#print axioms body
end AspisR1.Hist_DistinctBody
end
