import ExtractedReadonlyMeta

/-! Conditional runtime boundary only. These values record the owner and three
flags observed by the unchanged AccountInfo projection wrapper and reported by
the runtime loader. No SDK allocation/borrow semantics, caller reachability,
owner authentication, PDA validation, or custody theorem is asserted here. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1ReadonlyMeta

structure ReadonlyMetadata where
  owner : solana_pubkey.Pubkey
  is_signer : Bool
  is_writable : Bool
  executable : Bool

/-- One named R16 premise. Its satisfaction by actual runtime AccountInfo field
reads remains a runtime-boundary obligation; this is a Prop, not an axiom. -/
def R16ReadonlyMetadataProjection (observed runtime : ReadonlyMetadata) : Prop :=
  observed.owner = runtime.owner ∧ observed.is_signer = runtime.is_signer ∧
    observed.is_writable = runtime.is_writable ∧ observed.executable = runtime.executable

theorem readonly_success_iff_of_projection
    (observed runtime : ReadonlyMetadata) (expected : solana_pubkey.Pubkey)
    (hprojection : R16ReadonlyMetadataProjection observed runtime) :
    readonly_meta.readonly_meta_ok observed.owner expected observed.is_signer
      observed.is_writable observed.executable = ok (core.result.Result.Ok ()) ↔
      runtime.owner = expected ∧ runtime.is_signer = false ∧
        runtime.is_writable = false ∧ runtime.executable = false := by
  rcases hprojection with ⟨ho, hs, hw, he⟩
  rw [ReadonlyMetaProof.success_iff, ho, hs, hw, he]

#print axioms readonly_success_iff_of_projection
end AspisR1ReadonlyMeta
