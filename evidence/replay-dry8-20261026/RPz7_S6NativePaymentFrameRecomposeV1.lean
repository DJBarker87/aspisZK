import RPz7_S6NativePaymentCommonContentsV1
import S6SliceRecomposeV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativePaymentContents
open AspisR1TerminalDecoder
open pool_v1.payment_relation

/-- The digest frame refers to the actual encoder return, so its byte contents
are the same concrete encoder's symbolic chunk contents. -/
theorem encoded_digest_chunks (digest : Array U32 8#usize) (encoded : Array U8 32#usize)
    (h : atomic_statement.encode_digest_canonical digest=ok encoded) :
    AspisS6SourceCodec.DigestContents.chunks digest=encoded.val := by
  have hs := AspisS6NativeSnapshotEncodeTotal.digest_spec digest
  rw [h,WP.spec_ok] at hs
  exact hs.symm

theorem accepted_header_prefix (raw : Array U8 216#usize) (magic : Array U8 4#usize)
    (kind : pool_v1.historical_anchor.PoolV1TransitionKind)
    (h : AspisS6NativePaymentDecode.header_frame raw magic kind) :
    magic.val++[1#u8,(read_discriminant kind : U8),1#u8,0#u8]=raw.val.take 8 := by
  rcases h with ⟨hm,h4,h5,h6,h7⟩
  have hm' : raw.val.take 4=magic.val := by simpa [List.slice] using hm
  have hexpand := AspisS6SliceFrame.header_eight raw.val (by
    have hlen := raw.property
    scalar_tac)
  rw [hm',h4,h5,h6,h7] at hexpand
  exact hexpand.symm

/-- Complete 148-byte common prefix reconstructed from actual accepted header
and common decoder fields. No independent digest success premises. -/
theorem accepted_common_prefix (raw : Array U8 216#usize) (magic : Array U8 4#usize)
    (kind : pool_v1.historical_anchor.PoolV1TransitionKind)
    (common : CommonPublicV1)
    (header : AspisS6NativePaymentDecode.header_frame raw magic kind)
    (fields : AspisS6NativePaymentDecode.common_frame raw common) :
    common_prefix magic kind common=raw.val.take 148 := by
  rcases fields with ⟨hp,hd,hs,⟨anchor,ha,hab⟩,⟨nullifier,hn,hnb⟩,hv⟩
  have ha' := (encoded_digest_chunks common.anchor_root anchor ha).trans hab
  have hn' := (encoded_digest_chunks common.nullifier nullifier hn).trans hnb
  unfold common_prefix
  rw [accepted_header_prefix raw magic kind header,hp,hd,hs,ha',hn',hv]
  rw [AspisS6SliceFrame.take_append_slice raw.val 8 40 (by decide),
    AspisS6SliceFrame.take_append_slice raw.val 40 72 (by decide),
    AspisS6SliceFrame.take_append_slice raw.val 72 80 (by decide),
    AspisS6SliceFrame.take_append_slice raw.val 80 112 (by decide),
    AspisS6SliceFrame.take_append_slice raw.val 112 144 (by decide),
    AspisS6SliceFrame.take_append_slice raw.val 144 148 (by decide)]

#print axioms encoded_digest_chunks
#print axioms accepted_header_prefix
#print axioms accepted_common_prefix
end AspisS6NativePaymentContents
