# LPo return abstractions

No multiplication is verified by Kani. No natural-number field-operation stub
or assumption-based function contract is introduced.

| Stub | Domain/coverage | Named Lean association | Native callee association |
|---|---|---|---|
| LPo_any_inactive for E::from_le_bytes | All native Option<E> return bit patterns; no assumes or canonical restriction; actual input is32-byte range | LPo.View.decoder_spec derives the EXACT model return; LPo.View.model_product substitutes it; LPo.View.product_readset is universal over Option Wide | K008 actual parser iff canonical eight LE32 words, exact every output word |
| LPo_raw_inactive for E::from_le_bytes | Every256-bit E return represented by input32 raw bits, for assignment-only test; no claim these bytes are a field encoding | LPo.View.model_product preserves its supplied decoder value exactly in rest.inactive | K009 exact field preservation; K008 supplies real decoder separately |

These stubs enlarge possible returns; they never assume output correctness.
There is no assertion that an arbitrary stub choice equals the actual decoder.
The native range/assignment checks hold universally and are instantiated with
the independently established exact decoder. Native/Kani and compiler/library
association remain hybrid P6 evidence, not kernel verification of Rust.
