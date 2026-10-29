import NED_DigestCohorts
set_option autoImplicit false
noncomputable section
namespace NED_ScannerCohorts
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable

theorem account_body (d : Array U32 8#usize) (i : Usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body d i =
    AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body d i := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body
    AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body
    AspisR1AdapterReconstruct.aspis_core.field.P AspisR1TerminalDecoder.aspis_core.field.P
  rfl

theorem account_loop (d : Array U32 8#usize) (i : Usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.digest_is_canonical_loop d i =
    AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical_loop d i := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.digest_is_canonical_loop
    AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical_loop
  rw [funext (account_body d)]

theorem account (d : Array U32 8#usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.digest_is_canonical d =
    AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical d := account_loop d 0#usize

theorem profile_body (d : Array U32 8#usize) (i : Usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.digest_is_canonical_loop.body d i =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.digest_is_canonical_loop.body d i := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.digest_is_canonical_loop.body
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.digest_is_canonical_loop.body
    AspisR1AdapterReconstruct.aspis_core.field.P AspisR1TerminalDecoder.aspis_core.field.P
  rfl

theorem profile_loop (d : Array U32 8#usize) (i : Usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.digest_is_canonical_loop d i =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.digest_is_canonical_loop d i := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.digest_is_canonical_loop
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.digest_is_canonical_loop
  rw [funext (profile_body d)]

theorem profile (d : Array U32 8#usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.digest_is_canonical d =
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.digest_is_canonical d := profile_loop d 0#usize

theorem profile_result (d : Array U32 8#usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.digest_is_canonical d =
    ok (decide (NBD_DigestInduction.Canonical d)) := by
  rw [profile,NBD_DigestInduction.source]

theorem account_result (d : Array U32 8#usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.digest_is_canonical d =
    ok (decide (NBD_DigestInduction.Canonical d)) := by
  rw [account,NBD_DigestInduction.same_scanner,NBD_DigestInduction.source]

#print axioms account_body
#print axioms account_loop
#print axioms account
#print axioms profile_body
#print axioms profile_loop
#print axioms profile
#print axioms profile_result
#print axioms account_result
end NED_ScannerCohorts
