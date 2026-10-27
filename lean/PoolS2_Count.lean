import PoolS2_PrefixSource
set_option autoImplicit false
namespace AspisR1.PoolS2_Count
open Aeneas Aeneas.Std Result PoolS2_PrefixSource

theorem accepted (accounts : Slice Account) (expected : Usize) :
    pair_forest.require_exact_account_count accounts expected = ok (.Ok ()) ↔
      accounts.val.length = expected.val := by
  unfold pair_forest.require_exact_account_count
  by_cases same : Slice.len accounts = expected
  · have val : accounts.val.length = expected.val := by scalar_tac
    simp [same,val]
  · have val : accounts.val.length ≠ expected.val := by scalar_tac
    by_cases less : Slice.len accounts < expected <;> simp [same,val,less]

theorem short (accounts : Slice Account) (expected : Usize)
    (less : accounts.val.length < expected.val) :
    pair_forest.require_exact_account_count accounts expected =
      ok (.Err AdapterRw.solana_program_error.ProgramError.NotEnoughAccountKeys) := by
  have lt : Slice.len accounts < expected := by scalar_tac
  have ne : Slice.len accounts ≠ expected := by scalar_tac
  simp [pair_forest.require_exact_account_count,lt,ne]

theorem long (accounts : Slice Account) (expected : Usize)
    (more : expected.val < accounts.val.length) :
    pair_forest.require_exact_account_count accounts expected =
      ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidArgument) := by
  have lt : ¬ Slice.len accounts < expected := by scalar_tac
  have ne : Slice.len accounts ≠ expected := by scalar_tac
  simp [pair_forest.require_exact_account_count,lt,ne]

#print axioms accepted
#print axioms short
#print axioms long
end AspisR1.PoolS2_Count
