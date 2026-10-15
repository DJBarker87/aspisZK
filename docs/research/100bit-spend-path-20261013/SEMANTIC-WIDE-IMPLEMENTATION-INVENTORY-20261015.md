# Semantic terminal field-type inventory

This is a source inventory for a possible semantic cost experiment. It records the current Rust types and existing measurements; it does not propose a transcript change or claim that a WideExact implementation is protocol-equivalent.

Inspected worktree revision: `a17829a776d533d7cd0beeb1f8676dcc793a909c`.

| Source | SHA-256 |
|---|---|
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs` | `2bb7db64dc53c8a268e42b0fe46da64ab1afcb03d28bbec2569b2abc30cbc074` |
| `crates/aspis-r1-cost-probe/src/r1_semantic.rs` | `964f008a0841246fe3638ce2e492d12d18d78302565aa57f8c7df4d079579ce3` |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs` | `73f4b49dfae90be8a5cafd9d69eaf9ed06a01009f3daabc5627b42e6cf31c996` |
| `crates/aspis-r1-cost-probe/src/semantic_wire.rs` | `58c671cee016246aa464a35ba443009813581e4a53bce37dd528d048009f2db7` |
| `crates/aspis-r1-cost-probe/src/semantic.rs` | `75d83ce86b203023c3a9a9d35420853b6a5a9196b634a971859f6f4b98b0d0c5` |
| `crates/aspis-r1-cost-probe/src/host_semantic.rs` | `113a367ae1e01d8fbd808ce3756b87040fd31ab359d94bad50b7c55c89c284bf` |

## Current terminal and wire types

`aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::composition_parts` (lines 1216–1278) accepts `claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1]`, `point: &[QM31; 10]`, and `lambda`, `chi`, `theta: QM31`. It returns a `Result` whose value contains a `QM31` composition and QM31 opening/helper values. `terminal_parts` (1285–1310) adds a QM31 equality weight and `mu: QM31`, returning a QM31 original terminal plus QM31 openings.

The `define_variant_terminal!` macro (1348–1439) generates the private-transfer and withdrawal composition, unmasked-terminal, and masked-terminal functions. Their claim arrays, points, challenges, and results are all QM31. `r0::Public::terminal_qm31` (2044–2063) takes `&[[QM31; 29]; 3]`, `&[QM31; 10]`, and QM31 `Challenges`, selects the first 28 columns per point, and returns `Result<QM31, Error>`.

There is a public `r0::Public::terminal` at lines 2064–2102 whose result type is `WideExact`. Its inputs still include QM31 challenges and ten QM31 alpha values. On all-QM31 claims it calls `terminal_qm31` once and embeds the result. Otherwise it evaluates `terminal_qm31` at 26 QM31 points and interpolates the result into WideExact. The implementation comment characterizes this as exact polynomial base extension, not a probabilistic identity test. This API is an extension in the claims/output direction; it does not provide a field-generic `composition_parts` or WideExact challenge evaluator.

In the cost-probe path, `r1_semantic.rs::Verified` (lines 7–23) stores `alpha: [QM31;10]`, `claims: Box<[[QM31;29];3]>`, and under the prover feature `terminal` and `masked_terminal` as QM31. `verify_observed` calls `Public::terminal_qm31` (lines 103–124). Its helper `decode` (25–39) requires exactly `N*32` bytes, rejects nonzero upper 16 bytes of each 32-byte limb, and parses the lower half as QM31. `r1_wire.rs::row_shape`/`parse_record` (38–73) validates framing and canonical WideExact encodings, then for semantic rows 14 onward rejects a nonzero QM31 upper component. `decode_k` yields the corresponding QM31 values. `semantic_wire.rs::Challenges` (236–258) stores lambda, chi, theta, ten zero-check challenges, mu, eta as QM31; `begin` (260 onward) obtains them through `SemanticTranscript::semantic`. Its `with_alphas` merely embeds these K values as WideExact for diagnostic transcript history.

The separate `crates/aspis-r1-cost-probe/src/semantic.rs` path also calls `terminal_qm31`; `host_semantic.rs` calls the same API for the host-side semantic computation. The current caller therefore reaches the QM31 terminal even though surrounding proof rows use WideExact framing.

## Tests and measurements found

The pair-forest terminal module has these directly relevant unit tests:

- `honest_transfer_and_withdrawal_vanish_on_every_boolean_row` checks both variants on 1024 Boolean rows.
- `semantic_common_factor_kernels_equal_literal_off_domain` and `packed_range_shared_selector_equals_literal_off_domain` compare optimized and literal arithmetic on off-domain samples.
- `packed_public_digest_matches_all_transfer_and_withdrawal_bindings` checks digest factoring on Boolean rows and selected off-domain points.
- `output_occupancy_and_append_afterstate_fail_closed` checks selected invalid occupancy and a changed append frontier.

These tests exercise the QM31 evaluator and its factorizations; they are not a test of a separate WideExact terminal evaluator. `r1_wire.rs::validated_transcript_matches_checked_raw_path_for_every_row` tests equivalence between checked and validated transcript-sampling paths across rows. Cost-probe tests include the R1 framing/canonicality test `semantic_rows_reject_noncanonical_limbs_at_every_wide_position` in `tests/validated_prefix.rs`; no test there swaps `terminal_qm31` for a field-generic terminal.

The recorded P2 CU reconciliation in `evidence/p3-private-leaf-salts-20261013/P2-CU-RECONCILIATION.json` separates a `terminal` stage from the earlier `pairing` stage. It reports diagnostic tx1 CU 1,523,042 at the terminal stage versus 1,761,551 at pairing (238,509 saved), with tx2 unchanged at 1,518,138. The same file states that these are measurements across distinct source revisions on identical proof/public bytes and do not assert cryptographic or source-semantic equivalence. The saved P3 private-leaf-salts evidence reports successful terminal CU observations; for transfer/13, repeated same-public runs span 1,293,584–1,293,755 CU. Those artifacts measure the existing implementation and do not compare a WideExact semantic-terminal variant.

I searched the checked-out heads and local branches for `terminal_qm31`, `composition_parts`, and WideExact terminal declarations. The pair-forest implementation remains QM31-typed across the inspected historical branches. I found the `terminal` WideExact-returning interpolation adapter described above, but no alternate field-generic semantic terminal or WideExact `composition_parts` implementation in those sources.
