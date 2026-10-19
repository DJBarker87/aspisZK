# R17 query geometry batch-inversion proof packet

This packet freezes four focused Lean targets and their complete receipts, logs, preflights, and commands. No `.olean` binaries are included. The targets were checked with Lean 4.32 on the NUC in capped scopes with swap disabled.

## Proven statements

- `R1ZBatchInverseAlgebraV5`: a generic prefix-product/backward-pass recurrence. Given nonzero inputs, the reverse pass writes each input's inverse in original order.
- `R1ZBatchInverseSourceModelV4`: a list model of recording prefix products, then consuming them in reverse while constructing the forward-ordered inverse output.
- `R1ZQueryGeometryBatchInversionV3`: maps ordered query chunks to their five denominator slots, preserves flattening order, and connects one-query slots to `queryGeometryValues`.
- `R1ZQueryGeometryBatchInversionV6`: for an arbitrary `[start, stop)` range, models Rust's ordered query chunk concatenation and establishes the pointwise inverse result when the zero test succeeds.

The accepted theorem audits in the logs report only the usual Lean axioms (`propext`, `Classical.choice`, `Quot.sound`); no accepted theorem reports `sorryAx`.

## Source boundary

`source-pins/verifier.rs` is the exact pinned current source (SHA256 `93f36867c92f6f32434cc9e11090e573cb838bce362dc0ace8142ffcbc48fc41`). `QueryGeometry::for_range` is at lines 180–216. Its mathematical behavior is modeled: ordered denominator chunks, prefix products, and backward inversion.

This packet does **not** establish that the extracted Rust `Vec` implementation refines the list model. It also does not prove `fibre_point`'s table lookups and CM31 operations equal the stored formal circle point. Those actual-source adapters remain open. The exact `fast_domain.rs` snapshot is included at `source-pins/fast_domain.rs` (SHA256 `bf4b66a59f6a23d19adf6f0021dfa0b9ddb010d6611181d13374fec12c612151`) to pin the relevant implementation.

## Accepted run data

| Target | Source SHA256 | Object SHA256 | Exit / wall | Process RSS | Scope peak | Swap |
|---|---|---|---:|---:|---:|---:|
| Batch inverse algebra V5 | `8363bdfc1926f5cb9e21f2f0cd13964b4888bc6261d0229d9de14ca96e7e4622` | `349f2dcca4d2a41ca8bfe95cec02e2b2f1e0025e42ea79241de9dd9a3c48709e` | 0 / 1.205 s | 2,223,516 KiB | 255,643,648 B | 0 |
| Batch inverse source model V4 | `8bb564b3b089503bb9f133b06373b80d6d52484f1c671948443744b004d7fe5e` | `3c0123d47bcdbea26467713f535e966975b409b3c7be144227fac9bd23cc5310` | 0 / 1.104 s | 2,226,196 KiB | 253,870,080 B | 0 |
| Query batch inversion V3 | `d4f1d31853e4f22289cc71b38a765f1c7d7db2a8422c3e306ee484ff716c63b7` | `5a502d7fb9ad779ba8f8ba628e2b0c7c6dd40b5d2a2a5521db2b621810c86473` | 0 / 1.305 s | 2,748,964 KiB | 298,123,264 B | 0 |
| Query range inversion V6 | `ad992d8cdd85b34e7d22072f0e432468a9a3d743a1eaee87dce8bea2343e5f93` | `6a33158e16c64f7002e3f09d390f3d4c0327bf3efddf6d0fc79d0a37b2d646f1` | 0 / 1.405 s | 2,754,396 KiB | 297,259,008 B | 0 |

`SHA256SUMS` covers every packet file except itself. The manifest records exact source/object and evidence hashes.
