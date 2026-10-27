import RPz7_S6NativePaymentValidatorTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativePaymentEncodeTotal
open AspisR1TerminalDecoder
open pool_v1.payment_relation

@[step] theorem word_spec (value : U32) :
    aspis_core.field.M31.to_le_bytes value ⦃ _ => True ⦄ := by
  unfold aspis_core.field.M31.to_le_bytes
  rw [WP.spec_ok]
  trivial

private theorem array_slice_length {T : Type} {N : Usize} (a : Array T N) :
    (Array.to_slice a).length=N.val := by
  change a.val.length=N.val
  exact a.property

/-- TOTAL exact common-field writer, with its actual216-byte buffer carrier. -/
@[step] theorem common_write_spec (output : Array U8 216#usize) (magic : Array U8 4#usize)
    (kind : pool_v1.historical_anchor.PoolV1TransitionKind)
    (common : CommonPublicV1) :
    encode_common output magic kind common ⦃ _ => True ⦄ := by
  unfold encode_common POOL_OFFSET DEPLOYMENT_DOMAIN_OFFSET ANCHOR_SEQUENCE_OFFSET
    ANCHOR_ROOT_OFFSET NULLIFIER_OFFSET ASSET_ID_OFFSET AMOUNT_OR_RESERVED_OFFSET
  step*
  all_goals (simp_all only [array_slice_length] <;> scalar_tac)

theorem common_write_total (output : Array U8 216#usize) (magic : Array U8 4#usize)
    (kind : pool_v1.historical_anchor.PoolV1TransitionKind)
    (common : CommonPublicV1) :
    ∃ out, encode_common output magic kind common=ok out := by
  obtain ⟨out,h,_⟩ := spec_imp_exists (common_write_spec output magic kind common)
  exact ⟨out,h⟩

#print axioms word_spec
#print axioms common_write_total
end AspisS6NativePaymentEncodeTotal
