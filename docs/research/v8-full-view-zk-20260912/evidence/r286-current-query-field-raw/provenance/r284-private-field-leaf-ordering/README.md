# R284 QM31 field leaf ordering metadata

`order_metadata.py` follows the pinned Charon simple Type/Fun/Global traversal for exact R281 roots Fun0 and Fun1. It fails closed on trait references, missing rows, unknown typed-reference forms, or cycles. The R281 `has_errors=false` artifact and root-body inspection are hash-pinned. The roots have structured bodies and `item_meta.is_local=false`, because they are in the frozen `aspis_core` dependency; this structural condition is explicitly audited without inferring semantics.

R284 orders 12 reachable declarations: Type3, Fun8, Global1. Its graph has no trait references, missing declarations, unknown reference forms, or cycles. The output preserves every original declaration row and modifies only `translated.ordered_decls`; the audit includes all row hashes, dependency edges, and integer-ID census. This is order metadata only. It does not constitute LLBC translation, a source correspondence, a theorem, or release evidence. No translation/Lean action was run.

R281 input LLBC SHA-256: `6ffca95bc433f10b0b01db769cdb76c9f99421c0d7c3cfb7b4644af2e33b3f01`.
R281 body inspection SHA-256: `41d46d9da7ebc64e44d3100f57b788fbb80b0f0260122ccbc5f0d4395d3c5c9b`.
Pinned Charon reorder source SHA-256: `8a1176e29a51a83c82ff5a7df2aa11021e3e0c254e9fd6c656c0a92314ba2632`.
R284 generator SHA-256: `9a560b602deed3a1f04a3e21b5c7576045c4819b1f73fdf325a210ae9c70f19e`.
R284 ordered LLBC SHA-256: `37a693d55297515db02c3284f87226b8fc5f0df31cceeb3ec0d16460a69ddce5`.
R284 audit SHA-256: `819efb93eb816112da382df8705e458f57dbee7e40d982797d405ecbb102af0d`.
