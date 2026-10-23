import S6SourcePaymentCommonDecodeV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6SourceCodec.PaymentDecode
open AspisS6FiveUnrolledCodec
open aspis_statement.pool_v1.payment_relation

@[step] theorem header_spec (bytes : Array U8 216#usize) (magic : Array U8 4#usize)
    (kind : aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind) :
    require_header bytes magic kind ⦃ _ => True ⦄ := by
  unfold require_header POOL_V1_PAYMENT_STATEMENT_VERSION
    aspis_statement.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
    core.cmp.PartialEq.ne.trait_default Slice.Insts.CoreCmpPartialEqSlice
  step*

#print axioms header_spec
end AspisS6SourceCodec.PaymentDecode
