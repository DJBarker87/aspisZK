# Sampler source inventory

Read-only inventory captured from worktree revision `0dbaf0c8d576a8da71e031b89cef2c9083c67cca`. Paths and line numbers below refer to that worktree. SHA-256 hashes identify the exact files inspected; the inventory itself is hashed in `SAMPLER-SOURCE-INVENTORY.sha256`.

This records implementation steps and the remaining proof-bridge boundaries. It makes no cryptographic, probabilistic, security, or source-equivalence conclusion.

## Rust path and operations

The optimized long-division implementation under inspection is [`crates/aspis-r1-cost-probe/src/sampler.rs`](../../../crates/aspis-r1-cost-probe/src/sampler.rs). The crate labels itself an “UNPROVED COST PROBE” and an isolated P2 experiment in [`lib.rs`](../../../crates/aspis-r1-cost-probe/src/lib.rs:1-3) and its manifest; this inventory only describes the sampler code.

- **Block to limbs:** `qm31_sample` and `low_base_p_digits` initialize an eight-element `u32` array using `u32::from_le_bytes(block[4*i..4*i+4])` for `i = 0..8` ([`sampler.rs:8-10`](../../../crates/aspis-r1-cost-probe/src/sampler.rs:8), [`sampler.rs:29-32`](../../../crates/aspis-r1-cost-probe/src/sampler.rs:29)). Thus array index 0 contains bytes 0–3 as a little-endian word, through index 7 containing bytes 28–31.
- **One division pass:** Each `array::from_fn` closure starts `remainder = 0u64`, then traverses the mutable limb array with `iter_mut().rev()` ([`sampler.rs:11-19`](../../../crates/aspis-r1-cost-probe/src/sampler.rs:11), [`sampler.rs:32-40`](../../../crates/aspis-r1-cost-probe/src/sampler.rs:32)). For each limb, in array-index order 7 down to 0, it forms `(remainder << 32) | u64::from(*limb)`, stores `dividend / u64::from(P)` back as `u32`, and sets `remainder = dividend % u64::from(P)`. The closure returns that pass’s final remainder as `u32`.
- **Four/eight passes and digit order:** `qm31_sample` runs four passes and puts returned digits 0–3 into the QM31 constructor ([`sampler.rs:8-23`](../../../crates/aspis-r1-cost-probe/src/sampler.rs:8)). `low_base_p_digits` runs eight passes; after the passes it asserts in debug builds that quotient limbs 1–7 are zero and quotient limb 0 is at most 256, then returns `(digits, quotient[0])` ([`sampler.rs:29-46`](../../../crates/aspis-r1-cost-probe/src/sampler.rs:29)). Each pass appends one return value to the array produced by `array::from_fn`; pass 0 is the first returned digit. The implementation names these the low base-P digits in its comments ([`sampler.rs:6-7`](../../../crates/aspis-r1-cost-probe/src/sampler.rs:6), [`sampler.rs:26-28`](../../../crates/aspis-r1-cost-probe/src/sampler.rs:26)).
- **Ordinary sample:** `ordinary_sample` discards the final quotient, retains all eight returned digits, and calls `decode8` ([`sampler.rs:73-78`](../../../crates/aspis-r1-cost-probe/src/sampler.rs:73)).
- **Gamma increment/carry branches:** `gamma_sample` keeps the final quotient, calls `add_small_base_p(&mut digits, quotient + 1)`, and, if that reports a leftover carry, calls `add_small_base_p(&mut digits, 1)` once more; the second call has a debug assertion that it does not carry again ([`sampler.rs:80-92`](../../../crates/aspis-r1-cost-probe/src/sampler.rs:80)). `add_small_base_p` visits the mutable digit slice in increasing index order, so low digit first. At each position it computes a `u64` sum of the digit and addend, stores `sum % P`, carries `sum / P`, then returns whether a nonzero carry remains after the slice ([`sampler.rs:61-71`](../../../crates/aspis-r1-cost-probe/src/sampler.rs:61)).
- **Field construction:** `decode8` groups digits 0–3 into the first QM31 coordinate and digits 4–7 into the second, then calls `WideExact::new` ([`sampler.rs:48-59`](../../../crates/aspis-r1-cost-probe/src/sampler.rs:48)). `WideExact::new` canonicalizes both QM31 values ([`wide_exact.rs:54-59`](../../../crates/aspis-core/src/field/wide_exact.rs:54)); `canonical_qm31` reduces each of the four M31 representatives by `% P` ([`wide_exact.rs:273-286`](../../../crates/aspis-core/src/field/wide_exact.rs:273)). The documented limb order is `(c0.c0.a, c0.c0.b, c0.c1.a, c0.c1.b, c1.c0.a, c1.c0.b, c1.c1.a, c1.c1.b)`, with `decode8(d) = decode4(d[0..4]) + decode4(d[4..8])*v` ([`wide_exact.rs:5-20`](../../../crates/aspis-core/src/field/wide_exact.rs:5)). `P` is declared as `0x7fff_ffff` ([`field.rs:18-19`](../../../crates/aspis-core/src/field.rs:18)).

The core frozen sampler gives a source-side reference for the older reduction path: `block_rank` performs the same indexed little-endian word reads ([`r0_transcript.rs:89-94`](../../../crates/aspis-core/src/r0_transcript.rs:89)); `base_p_digits` uses the same high-to-low limb traversal and repeated division ([`r0_transcript.rs:124-136`](../../../crates/aspis-core/src/r0_transcript.rs:124)); and the field decoders plus ordinary/gamma construction are at [`r0_transcript.rs:138-171`](../../../crates/aspis-core/src/r0_transcript.rs:138). This is a source listing only, not a conclusion about correspondence.

## What the checked Lean results cover

[`SamplerWord.lean`](../../../docs/research/100bit-spend-path-20261013/lean/SamplerWord.lean:10) proves the Nat shift/OR packing identity and bounds the packed expression; its `machineStep` explicitly models the `UInt64` shift/OR, division/modulo and `UInt32.ofNat` conversions ([`SamplerWord.lean:39-100`](../../../docs/research/100bit-spend-path-20261013/lean/SamplerWord.lean:39)). [`SamplerWordPass.lean`](../../../docs/research/100bit-spend-path-20261013/lean/SamplerWordPass.lean:11) defines a recursive process over a `List UInt32` and proves the resulting quotient-digit numeral and remainder for that list ([`SamplerWordPass.lean:51-146`](../../../docs/research/100bit-spend-path-20261013/lean/SamplerWordPass.lean:51)). Its input is a list consumed head first; it does not itself decode `[u8; 32]`, construct the little-endian limb array, or show that the Rust mutable-array traversal/`array::from_fn` loop is this recursive function.

[`SamplerNatModel.lean`](../../../docs/research/100bit-spend-path-20261013/lean/SamplerNatModel.lean:14) defines repeated low-digit extraction and proves the four/eight-digit values are modulo `P^4` and `P^8` ([`SamplerNatModel.lean:35-52`](../../../docs/research/100bit-spend-path-20261013/lean/SamplerNatModel.lean:35)). It also proves a Nat/list `radix32_pass` statement for a high-to-low input digit list ([`SamplerNatModel.lean:101-108`](../../../docs/research/100bit-spend-path-20261013/lean/SamplerNatModel.lean:101)). The remainder/quotient identity for `machineProcess` is for an arbitrary supplied digit list and does not establish that list’s relationship to the Rust byte block.

For gamma, the Lean model defines `gammaDigits x` as `endAround P (x / P^8) (ordinaryDigits x)` ([`SamplerNatModel.lean:41-44`](../../../docs/research/100bit-spend-path-20261013/lean/SamplerNatModel.lean:41)). `endAround` adds quotient-plus-one to the low digit list and, exactly when the first carry is nonzero, adds one a second time ([`SamplerAddBridge.lean:39-43`](../../../docs/research/100bit-spend-path-20261013/lean/SamplerAddBridge.lean:39)). Its value theorem is a Nat-list result ([`SamplerAddBridge.lean:45-82`](../../../docs/research/100bit-spend-path-20261013/lean/SamplerAddBridge.lean:45)). No checked theorem listed here maps Rust’s mutable `u32` digit slice, `u64` sum, `% P`, `/ P`, Boolean carry test, and conditional second call to that list function.

## Remaining source-bridge operations to account for

At the inspected files and revisions, the following exact operational links remain outside the stated `SamplerWordPass` and `SamplerNatModel` results:

1. Decode the 32-byte block into the eight-element little-endian limb array and present those same limbs, in the required high-to-low sequence, to the Lean list model.
2. Relate Rust’s single mutable array traversal (`iter_mut().rev()`) to one full Lean `machineProcess` pass, including the in-place quotient array and the emitted remainder digit.
3. Relate four/eight successive Rust `array::from_fn` passes, including final quotient extraction/throwaway, to iteration of the proved list-pass result.
4. Relate the Rust little-endian digit-slice `u64` add/carry loop and the conditional second add-one call to the Nat `endAround`/`addDigits` definition, including the output array order.
5. Relate direct `M31`/`CM31` construction and `WideExact::new` canonicalization to the positional digit tuple/field decoding representation.

These are bridge items, not assessed here for difficulty or sufficiency. No premise has been added and no source equivalence is asserted.

## File hashes

SHA-256 values were computed from the worktree files listed below at the revision named above. The Rust files have no worktree modifications at capture time; the two listed word Lean files are untracked task files in this worktree, so their content hashes are especially important identifiers.

| Path | SHA-256 |
|---|---|
| `crates/aspis-r1-cost-probe/src/sampler.rs` | `be426dfc4049682ef2d90940ee42bf9cffbec2db1d2d9b965e9c14e491948b8c` |
| `crates/aspis-core/src/r0_transcript.rs` | `2a315219d20069742c7c07e2a1ab8ee283865be3c607fdde2cf6975ad1813fc1` |
| `crates/aspis-core/src/field.rs` | `3046536d04e84357c7df7bd742ec9839d1e1dc47ccc0ecaa59eb79ddec453c68` |
| `crates/aspis-core/src/field/wide_exact.rs` | `56c26ce33cd0caee95f33474bfc351c5409503b6af665dba7c8837d6ec1068ea` |
| `docs/research/100bit-spend-path-20261013/lean/SamplerNatModel.lean` | `e2041176802dd226819b72c83ad311c601986ebfb37ce5544402d55be68463e6` |
| `docs/research/100bit-spend-path-20261013/lean/SamplerWordPass.lean` | `16f37454a6d5e3672ee0f3a5c6c195926c3d9e64c4d7d423b79d1eabd87d6b11` |
| `docs/research/100bit-spend-path-20261013/lean/SamplerWord.lean` | `8206a4a664485894d4e3aff5443acfcff389445fb4e4c341269a9fd2aa440598` |
| `docs/research/100bit-spend-path-20261013/lean/SamplerPass.lean` | `631e025882495fcc5b2a402b9b002edc594080269c37553fd165499e61b9e0dd` |
| `docs/research/100bit-spend-path-20261013/lean/SamplerAddBridge.lean` | `22a9d1474abe3ebbefaae867a287f15e36c572a2d51ff9b846f5478c713496a8` |
| `docs/research/100bit-spend-path-20261013/lean/SamplerDigits.lean` | `63f68242e997faf598724e969130acd60085382c673c60d2819cbfbc19b67ed9` |

No build or test was run for this read-only inventory.
