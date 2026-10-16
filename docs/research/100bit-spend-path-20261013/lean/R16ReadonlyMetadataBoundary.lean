import ExtractedReadonlyMeta

/-! Conditional runtime boundary only. These values record the owner and three
flags observed by the AccountInfo account and buffer projection wrappers and reported by
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

/-- One named R16 premise shared by `require_readonly_account` and
`require_readonly_buffer`. The account guard consumes owner plus flags; the
buffer guard consumes just the three flags. Its satisfaction by actual runtime
AccountInfo field reads remains a runtime-boundary obligation; this is a Prop,
not an axiom. No additional projection or custody premise is introduced. -/
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

theorem readonly_buffer_success_iff_of_projection
    (observed runtime : ReadonlyMetadata)
    (hprojection : R16ReadonlyMetadataProjection observed runtime) :
    readonly_meta.readonly_buffer_meta_ok observed.is_signer observed.is_writable
      observed.executable = ok (core.result.Result.Ok ()) ↔
      runtime.is_signer = false ∧ runtime.is_writable = false ∧ runtime.executable = false := by
  rcases hprojection with ⟨_, hs, hw, he⟩
  rw [ReadonlyMetaProof.buffer_success_iff, hs, hw, he]

/-- The same single runtime projection premise discharges both wrapper guards.
The owner condition is present only for the account guard; custody is separate. -/
theorem readonly_guards_success_iff_of_projection
    (observed runtime : ReadonlyMetadata) (expected : solana_pubkey.Pubkey)
    (hprojection : R16ReadonlyMetadataProjection observed runtime) :
    (readonly_meta.readonly_meta_ok observed.owner expected observed.is_signer
      observed.is_writable observed.executable = ok (core.result.Result.Ok ()) ↔
      runtime.owner = expected ∧ runtime.is_signer = false ∧
        runtime.is_writable = false ∧ runtime.executable = false) ∧
    (readonly_meta.readonly_buffer_meta_ok observed.is_signer observed.is_writable
      observed.executable = ok (core.result.Result.Ok ()) ↔
      runtime.is_signer = false ∧ runtime.is_writable = false ∧ runtime.executable = false) := by
  exact ⟨readonly_success_iff_of_projection observed runtime expected hprojection,
    readonly_buffer_success_iff_of_projection observed runtime hprojection⟩

#print axioms readonly_guards_success_iff_of_projection
#print axioms readonly_buffer_success_iff_of_projection
#print axioms readonly_success_iff_of_projection
end AspisR1ReadonlyMeta
