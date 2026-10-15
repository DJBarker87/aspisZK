# Semantic record codec focused evidence

This bundle contains the typed byte-model for semantic record payloads at rows 0–24. The index-dependent `RowPayload` restricts empty, C2-root, mask-sum, and polynomial values to their corresponding row classes. It composes the existing exact five-byte record frame, 32-byte low-Wide and 896-byte coefficient codecs, and state byte representation. The polynomial degree bound is reused from the coefficient codec.

This target establishes codec-level encode/decode behavior only. It does not prove that the Rust parser/caller has the same behavior, nor connect the decoded C2 root to authenticated C2 words.

Source base: `8e6c2b4cba1c54fe165f7436f5fc3ada1e1ae0f3`. Target: `R1SemanticRecordCodec`. Attempts a–d failed during proof plumbing; e is green. All exact source snapshots, receipts, stdout logs, time logs, and source-hash sidecars are retained. Receipt e records exit 0, 2.33 seconds, peak RSS 3,340,536 KiB, zero swap, and 4/6 GiB memory caps with 128 task cap. Five declarations have axiom reports; they depend on `[propext, Quot.sound]` or `[propext, Classical.choice, Quot.sound]` as listed in the manifest.

The object archive contains only the final target object. Direct imports and their source/object hashes, plus runner and environment pins, are recorded in `source-manifest.json`.
