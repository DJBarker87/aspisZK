import R1SemanticPrefixCodec

/-! Lightweight row-14 projection reused by the source-side initial-claim
bridge. This is the codec-level mask-sum claim, not an assertion about the
true sum of a hidden mask. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawSemanticPrefixMaskClaim
open AspisR1.SemanticRecordCodec AspisR1.SemanticCoefficientCodec

def claimAt14 (values : SemanticPrefixCodec.Full) : LowWide :=
  match values ⟨14, by omega⟩ with
  | ⟨.empty, h⟩ => False.elim (by simpa [validRow] using h)
  | ⟨.c2Root _, h⟩ => False.elim (by simpa [validRow] using h)
  | ⟨.maskSum value, _⟩ => value
  | ⟨.polynomial _, h⟩ => False.elim (by simpa [validRow] using h)

theorem claimAt14_payload (values : SemanticPrefixCodec.Full) :
    (values ⟨14, by omega⟩).val = .maskSum (claimAt14 values) := by
  unfold claimAt14
  cases values ⟨14, by omega⟩ with
  | mk payload hvalid =>
      cases payload with
      | empty => exact False.elim (by simpa [validRow] using hvalid)
      | c2Root root => exact False.elim (by simpa [validRow] using hvalid)
      | maskSum value => rfl
      | polynomial coefficients => exact False.elim (by simpa [validRow] using hvalid)

#print axioms claimAt14_payload
end AspisR1.RawSemanticPrefixMaskClaim
end
