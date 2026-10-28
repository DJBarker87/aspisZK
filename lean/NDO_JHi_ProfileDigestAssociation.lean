import NDO_JHi_DigestAssociation
import NDO_JFu_DigestCheck
set_option autoImplicit false
namespace AspisR1.JHi_ProfileDigestAssociation
open Aeneas Aeneas.Std Result

theorem source (q : Array U32 8#usize) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.digest_is_canonical q=
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.digest_is_canonical q := by
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.digest_is_canonical
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.digest_is_canonical
  unfold AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.digest_is_canonical_loop
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.digest_is_canonical_loop
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.digest_is_canonical_loop.body
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.digest_is_canonical_loop.body
    AspisR1AdapterReconstruct.aspis_core.field.P AspisR1TerminalDecoder.aspis_core.field.P
  rfl
#print axioms source

theorem canonical (q : Array U32 8#usize) (h : JFu_DigestCanonical.Canonical q) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.digest_is_canonical q=ok true := by
  rw [source]
  exact JFu_DigestCheck.source q h
#print axioms canonical
end AspisR1.JHi_ProfileDigestAssociation
