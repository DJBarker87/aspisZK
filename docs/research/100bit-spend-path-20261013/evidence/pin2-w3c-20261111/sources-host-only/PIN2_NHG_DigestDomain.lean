import PIN2_NHG_Final
import NGX_SemanticRuntime

/-! PIN2 W3c (2026-11-11): `NHG_Lengths.digest_domain` against the PIN2
generated `public_bytes`.  Same statement as the release theorem with the
carrier `NHG_Serializer.Public` replaced by the PIN2 carrier; the size premise
of `NGX_SemanticRuntime.seed_domain` is W3b's `PIN2_NHG_Final.seed_size`
(<= 1524 <= 57607).  NOT COMPILED on the Mac: `NGX_SemanticRuntime` sits above
`NGK_COMBINED_IMPORT` / `RPx_Deployed` (4,529 unbuilt affected imports, among
them the NDO_JF* fixtures and the FIz *OnRun modules); host replay target. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.PIN2_NHG_DigestDomain

theorem digest_domain
    (q : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (out : alloc.vec.Vec U8)
    (h : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes q =
      ok (.Ok out)) (domain tag length pub root : Nat) :
    (NGX_SemanticRuntime.seedViews domain tag length pub root out.val.length).length ≤ 9 ∧
    ∀ v ∈ NGX_SemanticRuntime.seedViews domain tag length pub root out.val.length, v.2 ≤ 57607 :=
  NGX_SemanticRuntime.seed_domain _ _ _ _ _ _ (AspisR1.PIN2_NHG_Final.seed_size q out h)

#print axioms digest_domain
end AspisR1.PIN2_NHG_DigestDomain
