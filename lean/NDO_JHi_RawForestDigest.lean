import NDO_JHi_ProfileDigestAssociation
set_option autoImplicit false
namespace AspisR1.JHi_RawForestDigest
open Aeneas Aeneas.Std Result

theorem source (q : Array U32 8#usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.digest_is_canonical q=
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.digest_is_canonical q := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.digest_is_canonical
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.digest_is_canonical
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.digest_is_canonical_loop
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.digest_is_canonical_loop
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.digest_is_canonical_loop.body
    AspisR1AdapterReconstruct.aspis_core.field.P AspisR1TerminalDecoder.aspis_core.field.P
  rfl
#print axioms source
end AspisR1.JHi_RawForestDigest
