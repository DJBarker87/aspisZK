# Substitutions and domains

No multiplication, SHA implementation, writable static, Option<fn>, function
pointer observer, proof_for_contract or stub_verified is used. The actual
sampler is not replaced by an assumed successful callee.

| Boundary substitution | Model law / domain | Credit and limit |
|---|---|---|
| Pair digest logging oracle | NGQ_Effects.materialize_erasure, NGQ_MaterializeChain.normalized/run; immutable32-byte state plus one tag byte, arbitrary complete32-byte reply, ordered local log | Returning native pair cuts only. Digest value=H remains P1/RuntimeSyscall/SHA realization trust. |
| Absorb logging oracle | NGQ_Effects.absorb_erasure and NGQ_DigestBridge.observed (emitted NGC reference); ordered4 descriptors:32 state,2 tag,4 LE length,payload<=8192, row<=95 | Actual absorb function returns unchanged arbitrary reply; full descriptor bytes verified by arbitrary window. |
| Prescribed ptr::copy_nonoverlapping stub | Exact KMX_copy_stubs.patch SHA bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67; KMX_CopyMeaning value/frame laws; T:Copy | Selected positive and corrupted-byte controls under same KMX/dependency/feature configuration. No competing copy stub. |
| Outer scan local callee boundary | Arbitrary complete QueryScan reply and Bool, exact mutable prestate/block log; NGQ_SamplerDriver.source / NGQ_SamplerTrace.source describe the model step/first-stop fold | Frame/argument fragment, not a completed scanner law. Caller scan invariant len<=22/draws<=64. |
| Post-membership branch | Arbitrary Bool reply, len<=22/draws<=64, full accepted frame; NGQ_SamplerStep fresh/duplicate laws | Split of timed-out K044. The actual contains callee association remains OPEN; no assumed mathematical membership installed. |
| Decoder call and tail boundary | Arbitrary typed full Result (all3 QuerySampleError constructors and arbitrary payloads),22 words and selected32-byte state; NGQ_TraceErase.finish_success/finish_rejected and NGQ_Embed.total | No success-only restriction. This does not certify the decoder implementation. |
| Evaluated from_m31 arguments | AspisS1M31Embedding.Total.source_total/embed_total and NGQ_Embed.total/finish; all rawU32 | Exact emitted constructor installed; all22 evaluated calls are preserved before totality justifies trace erasure. |

The NGC digest reference is reused with emitted definition bytes pinned by
NGQ_DIGEST_PROVENANCE.json, no new extraction. NGC_K082–K085 cover 0..9 immutable
parts, each<=57607; this caller uses4 parts<=8192 or2 parts<=32. No field-product
stub is needed, so LPh multiplication stub table is not extended. Retained
native semantic transport is reclassification of trust, never trust removal.
