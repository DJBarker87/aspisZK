import NBN_LateSummary
import NBN_AfterstateDecoderDependency
import NBN_IteratorAssociation
set_option autoImplicit false
noncomputable section
namespace NBN_U03
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

theorem conditional
    (encode : NBN_EncoderSummary.Encode) (decode : NBN_AfterDecodeTypes.Decode)
    (NBN_Dep_DigestEncodeCanonical : NBN_DigestResultDependency.NBN_Dep_DigestEncodeCanonical encode)
    (NBN_Dep_DigestDecode : NBN_AfterDecodeTypes.NBN_Dep_DigestDecode decode) :
    (∀ a, NBN_EncoderSummary.after encode a = pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 a) ∧
    (∀ s out, NBN_EncoderSummary.live encode s out = pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1 s out) ∧
    (∀ s out, NBN_LateSummary.run encode s out = pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1 s out) ∧
    (∀ bytes, NBN_AfterstateDecoderDependency.run decode bytes = pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1 bytes) :=
  ⟨NBN_EncoderSummary.after_source encode NBN_Dep_DigestEncodeCanonical,
    NBN_EncoderSummary.live_source encode NBN_Dep_DigestEncodeCanonical,
    NBN_LateSummary.source encode NBN_Dep_DigestEncodeCanonical,
    NBN_AfterstateDecoderDependency.source decode NBN_Dep_DigestDecode⟩

#print axioms conditional
end NBN_U03
