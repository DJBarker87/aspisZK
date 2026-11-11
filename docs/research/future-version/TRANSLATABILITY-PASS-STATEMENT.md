# Aspis translatability pass: statement side (aspis-statement)

Status: target not yet established. This note records which `aspis-statement` functions on the
Aspis verifier's on-chain path translate to Lean under the deployed feature set, the source changes
made so that the remaining ones translate, and the gates those changes passed. These are tool runs,
tests and measurements. A translated function is not a verified function, and nothing here is
proved.

Worker: statement side of the overnight translatability pass, 2026-11-11. Base source: the head's
source `src-xp1` (head 7dffe3e2a93 for the crates; host `SOURCE_REVISION` 4045ecbdda3), then
`src-base2` (the head plus a verifier optimisation in `fused.rs`/`multiproof.rs` and the sampler
rewrite). `crates/aspis-statement` is byte-identical in `src-xp1`, `src-base2` and the R1 pin
c7593d23fdc (`git diff --stat c7593d23fdc 7dffe3e2a93 -- crates/aspis-statement` is empty), so
every function left untouched is text-identical to c7593d23fdc.

## 1. How the classification was run

- Scope: Charon started from `pool_v1::pair_forest_semantic_terminal::r0::Public::terminal_qm31` and
  `Public::public_bytes`, the two statement entries the verifier calls (`r1_semantic.rs` lines 70
  and 305), run on the `aspis-statement` crate itself with `aspis_core::field`,
  `aspis_core::state_only_hiding` and `aspis_core::state_only_prefix::r0` included and
  `aspis_core::field::wide_exact` opaque.
- Deployed feature set, exactly: `r0,pool-v1-kernel` (from the verifier and program manifests),
  the nine `pool-v1-pair-forest-*-audit` features that `optimized-terminal` enables (with their
  implied features), and `aspis-core/future-fast-kmul,future-fast-prepared,future-fast-square,future-lazy-horner`
  (enabled by the deployed program). Overflow checks on, as in the verifier-crate recipe.
- Tools: the second pair (Charon 454586e9, Aeneas 0d21a9ec, nightly-2026-09-17), with the probe's
  command lines and environment (`EXTRACTION-PROBE.md` 1.2), through `fv_slot.sh`. The first pair
  was also run: its Charon succeeds (T2-C02), its Aeneas stops with an uncaught `Not_found` on this
  scope without naming a function (T2-A02, exit 2), as the probe found on the verifier scope
  (finding 5). All verdicts below are therefore second-pair verdicts. The privacy lead's combined
  translator was not used.
- Lean: Lean 4.32.0 against the L187 objects through `fv_lean.sh`, with the probe's header
  adaptation and shim (`AspisXPNewLib`) and, for the final emission, a two-definition shim of this
  pass (section 5).
- Runner scripts: `evidence/future-version-20261111/host/fv_tp2_charon.sh`,
  `fv_tp2_aeneas.sh`, `fv_tp2_release_checks.sh`; specs in `translatability/statement/specs/`.

Reachability: 85 `aspis-statement` functions (closure and `Clone` instances not counted) are in
Charon's output for the two entries (T2-C01, 401 declarations, LLBC sha256
3eda1970d859f0e1845a9c4ae6515834fe35f4743ddc421262bde3524ff92442). Not reached under the deployed
features, by the same output: `leading_pair` (only `leading_pair_packed` is), `pattern_values_literal`,
the `*_literal` and row-major semantic kernels, `public_digest_lanes`. The five functions the privacy
lead reserved (`endpoint_counts` twice, `build_pool_v1_pair_forest_copy_registry_v1`,
`sparse_eq_weights`, the closure in `state_only_copy_helper_sum`) are not in this output, nor in the
third worker's whole-program run (T3-C01).

Codec files. `payment_relation.rs` and `pair_tree_profile.rs` are reached by the account and
statement decoders (another worker's scope), not by the semantic check. A separate run from those
two modules (T2-C03/T2-A03) gives Aeneas errors only in witness and prover functions
(`witness_digest_is_canonical`, `spend::derive_owner_key`, `note_commitment`, `derive_nullifier`
and the function-item instances of `digest_is_canonical` and `hash_fields` they use), none on the
verifier's path. The record codecs and the serializer are left byte-identical, as the soundness
lead requires.

## 2. Classification (as found, deployed features, second pair)

Aeneas without `-abort-on-error` (T2-A01) rejected exactly two functions. The emitted Lean
(T2-L01-Funs, exit 1) had errors in exactly three Aspis declarations and two standard-library
instances. Columns: result as found; the R1 row status read from the soundness lead's table
(`ONCHAIN-PATH-EXTRACTION-STATUS-20261111.md`, origin/research), where "rewritten-crate model
(probe crate)" means the R1 gate is an emission of `aspis_r1_mask_extraction_probe` built with only
`r0,pool-v1-kernel`; whether the delivered text is identical to c7593d23fdc; result after this pass.

| Function | File | As found | R1 row status | Text identical to c7593d23fdc | After this pass |
|---|---|---|---|---|---|
| `accumulate_endpoint_selector_tensor_basis` | pair_forest_copy_terminal.rs | translates; elaborates | no model (deployed audit kernel: equality with the unoptimised kernel owed) | yes | unchanged |
| `build_copy_tag_coordinate_offsets` | pair_forest_copy_terminal.rs | translates; elaborates | not in table | yes | unchanged |
| `build_copy_tag_terms` | pair_forest_copy_terminal.rs | translates; elaborates | not in table | yes | unchanged |
| `build_group_local_coordinates` | pair_forest_copy_terminal.rs | translates; elaborates | not in table | yes | unchanged |
| `build_pattern_local_coordinates` | pair_forest_copy_terminal.rs | translates; elaborates | not in table | yes | unchanged |
| `copy_residual` | pair_forest_copy_terminal.rs | translates; elaborates | rewritten-crate model (probe crate) | yes | unchanged |
| `copy_tag_coordinate_dot` | pair_forest_copy_terminal.rs | translates; elaborates | no model (deployed audit kernel: equality with the unoptimised kernel owed) | yes | unchanged |
| `copy_tag_coordinate_value` | pair_forest_copy_terminal.rs | translates; elaborates | no model (deployed audit kernel: equality with the unoptimised kernel owed) | yes | unchanged |
| `evaluate_with_selectors` | pair_forest_copy_terminal.rs | translates; elaborates | rewritten-crate model (probe crate) + hand model | yes | unchanged |
| `finish_pattern_basis_values` | pair_forest_copy_terminal.rs | translates; elaborates | no model (deployed audit kernel: equality with the unoptimised kernel owed) | yes | unchanged |
| `finish_selector_tensor_basis` | pair_forest_copy_terminal.rs | translates; elaborates | hand model | yes | unchanged |
| `lift_m31` | pair_forest_copy_terminal.rs | translates; elaborates | settled | yes | unchanged |
| `link_weight` | pair_forest_copy_terminal.rs | translates; elaborates | settled | yes | unchanged |
| `pattern_values` | pair_forest_copy_terminal.rs | translates; elaborates | settled | yes | unchanged |
| `pattern_values_windowed` | pair_forest_copy_terminal.rs | does NOT translate: "Joining region abstractions containing shared loans whose shared value contains borrows is not supported yet" at pair_forest_copy_terminal.rs 299:8-302:9 (local closure `window`) | no model (deployed audit kernel: equality with the unoptimised kernel owed) | no | rewritten (batch tp2-b1, closure made the named function `pattern_window`); translates; Lean elaborates |
| `qm31_sum_products_up_to4` | pair_forest_copy_terminal.rs | translates; elaborates | hand model | yes | unchanged |
| `selected_binary_weight` | pair_forest_copy_terminal.rs | translates; elaborates | no model (deployed audit kernel: equality with the unoptimised kernel owed) | yes | unchanged |
| `Selectors::active` | pair_forest_copy_terminal.rs | translates; elaborates | settled | yes | unchanged |
| `Selectors::active_mask_basis` | pair_forest_copy_terminal.rs | translates; elaborates | no model (deployed audit kernel: equality with the unoptimised kernel owed) | yes | unchanged |
| `Selectors::at_point` | pair_forest_copy_terminal.rs | translates; elaborates | rewritten-crate model (probe crate) | yes | unchanged |
| `Selectors::boxed_at_point` | pair_forest_copy_terminal.rs | translates; elaborates | rewritten-crate model (probe crate) | yes | unchanged |
| `Selectors::eq` | pair_forest_copy_terminal.rs | translates; elaborates | not in table | yes | unchanged |
| `Selectors::expand` | pair_forest_copy_terminal.rs | translates; elaborates | rewritten-crate model (probe crate) | yes | unchanged |
| `Selectors::row` | pair_forest_copy_terminal.rs | translates; elaborates | rewritten-crate model (probe crate) | yes | unchanged |
| `absorption_lanes_factored` | pair_forest_semantic_terminal.rs | translates; elaborates | no model (deployed audit kernel: equality with the unoptimised kernel owed) | yes | unchanged |
| `add_occupancy_lanes` | pair_forest_semantic_terminal.rs | translates; elaborates | rewritten-crate model (probe crate) | yes | unchanged |
| `add_path_lanes` | pair_forest_semantic_terminal.rs | translates; elaborates | rewritten-crate model (probe crate) | yes | unchanged |
| `add_preweighted` | pair_forest_semantic_terminal.rs | translates; elaborates | rewritten-crate model (probe crate) | yes | unchanged |
| `add_preweighted_shared_selector` | pair_forest_semantic_terminal.rs | translates; elaborates | no model (deployed audit kernel: equality with the unoptimised kernel owed) | yes | unchanged |
| `add_schedule_lanes` | pair_forest_semantic_terminal.rs | translates; elaborates | rewritten-crate model (probe crate) + hand model | yes | unchanged |
| `add_value_lanes` | pair_forest_semantic_terminal.rs | translates; elaborates | rewritten-crate model (probe crate) + hand model | yes | unchanged |
| `append_level_packed_selector_tensor` | pair_forest_semantic_terminal.rs | translates; elaborates | hand model | yes | unchanged |
| `append_levels_packed_selector_tensor` | pair_forest_semantic_terminal.rs | translates; elaborates | hand model | yes | unchanged |
| `bounded_append_carry` | pair_forest_semantic_terminal.rs | translates; elaborates | settled | yes | unchanged |
| `composition_parts` | pair_forest_semantic_terminal.rs | translates; Lean does NOT elaborate: Prop/Bool mismatch in the emitted withdrawal-amount guard; the array `IntoIter` iterator instance used by `into_iter().rev()` does not elaborate against the R1 library (`fold`, `rev` not fields of its `Iterator`) | rewritten-crate model (probe crate) + hand model | no | rewritten (batch tp2-b2c: probe-crate index loops for the two Horner loops; guard moved unchanged into `invalid_withdrawal_amount`); translates; Lean elaborates |
| `copy_variant` | pair_forest_semantic_terminal.rs | translates; elaborates | settled | yes | unchanged |
| `empty_root` | pair_forest_semantic_terminal.rs | translates; elaborates | settled | yes | unchanged |
| `equality_value` | pair_forest_semantic_terminal.rs | translates; elaborates | rewritten-crate model (probe crate) | yes | unchanged |
| `initial_variant_selectors` | pair_forest_semantic_terminal.rs | translates; elaborates | settled | yes | unchanged |
| `left_digest_packed_selector_tensor` | pair_forest_semantic_terminal.rs | translates; elaborates | no model (deployed audit kernel: equality with the unoptimised kernel owed) | yes | unchanged |
| `lift_m31` | pair_forest_semantic_terminal.rs | translates; elaborates | rewritten-crate model (probe crate) | yes | unchanged |
| `occupancy_lanes_factored` | pair_forest_semantic_terminal.rs | translates; elaborates | no model (deployed audit kernel: equality with the unoptimised kernel owed) | yes | unchanged |
| `optional_carry_packed_selector_tensor` | pair_forest_semantic_terminal.rs | translates; elaborates | no model (deployed audit kernel: equality with the unoptimised kernel owed) | yes | unchanged |
| `optional_recipient_packed_selector_tensor` | pair_forest_semantic_terminal.rs | translates; elaborates | no model (deployed audit kernel: equality with the unoptimised kernel owed) | yes | unchanged |
| `path_lanes_factored` | pair_forest_semantic_terminal.rs | translates; elaborates | no model (deployed audit kernel: equality with the unoptimised kernel owed) | yes | unchanged |
| `poseidon_selectors` | pair_forest_semantic_terminal.rs | translates; elaborates | settled | yes | unchanged |
| `private_public` | pair_forest_semantic_terminal.rs | translates; elaborates | translatable as is | yes | unchanged |
| `public_digest_packed` | pair_forest_semantic_terminal.rs | translates; elaborates | hand model | yes | unchanged |
| `public_digest_packed_selector_tensor` | pair_forest_semantic_terminal.rs | translates; elaborates | hand model | yes | unchanged |
| `Public::public_bytes` | pair_forest_semantic_terminal.rs | translates; elaborates | hand model | yes | unchanged |
| `Public::public_bytes::fields` | pair_forest_semantic_terminal.rs | translates; elaborates | not in table | yes | unchanged |
| `Public::public_bytes::frontier` | pair_forest_semantic_terminal.rs | translates; elaborates | not in table | yes | unchanged |
| `Public::semantic` | pair_forest_semantic_terminal.rs | translates; elaborates | translatable as is | yes | unchanged |
| `Public::terminal_qm31` | pair_forest_semantic_terminal.rs | translates; Lean does NOT elaborate: `core::result::Result::map` absent from the R1 library | rewritten-crate model (probe crate) + hand model | yes | unchanged; library item `core.result.Result.map` added in the test shim AspisTP2NewLib; Lean elaborates |
| `reconstruct_10` | pair_forest_semantic_terminal.rs | translates; Lean does NOT elaborate: slice-iterator `next_back` absent from the R1 library | rewritten-crate model (probe crate) | yes | unchanged; library item `core.slice.iter.IteratorSliceIter.next_back` added in the test shim AspisTP2NewLib; Lean elaborates |
| `scalar_lanes` | pair_forest_semantic_terminal.rs | translates; elaborates | settled | yes | unchanged |
| `selected_claim` | pair_forest_semantic_terminal.rs | translates; elaborates | rewritten-crate model (probe crate) | yes | unchanged |
| `semantic_initial_and_absorption` | pair_forest_semantic_terminal.rs | translates; elaborates | rewritten-crate model (probe crate) + hand model | yes | unchanged |
| `semantic_packed` | pair_forest_semantic_terminal.rs | translates; elaborates | rewritten-crate model (probe crate) + hand model | yes | unchanged |
| `sum_high` | pair_forest_semantic_terminal.rs | translates; elaborates | settled | yes | unchanged |
| `terminal_parts` | pair_forest_semantic_terminal.rs | translates; elaborates (failed only through its callee composition_parts) | rewritten-crate model (probe crate) + hand model | yes | unchanged |
| `validate_transition` | pair_forest_semantic_terminal.rs | translates; elaborates | settled | yes | unchanged |
| `variant_expected_output` | pair_forest_semantic_terminal.rs | translates; elaborates | settled | yes | unchanged |
| `withdrawal_public` | pair_forest_semantic_terminal.rs | translates; elaborates | translatable as is | yes | unchanged |
| `evaluate_state_only_poseidon_oracle_projected` | state_only_poseidon.rs | translates; elaborates (array `into_iter().fold` and `RangeInclusive` fold are std axioms in the emission) | rewritten-crate model (probe crate) | yes | unchanged |
| `extension_from_raw_limbs` | state_only_poseidon.rs | translates; elaborates | rewritten-crate model (probe crate) | yes | unchanged |
| `extension_limbs` | state_only_poseidon.rs | translates; elaborates | settled | yes | unchanged |
| `external_linear_lazy` | state_only_poseidon.rs | does NOT translate: Aeneas "Unimplemented" at state_only_poseidon.rs 156:8-172:9 (core::array::from_fn closure capturing the loop variable `output`) | rewrite needed | no | rewritten (batch tp2-b1, probe-crate text verbatim); translates (abort-on-error run exit 0); Lean elaborates |
| `external_linear_packed` | state_only_poseidon.rs | translates; elaborates | rewritten-crate model (probe crate) | yes | unchanged |
| `external_local_packed` | state_only_poseidon.rs | translates; elaborates | rewritten-crate model (probe crate) | yes | unchanged |
| `external_local_packed_raw` | state_only_poseidon.rs | translates; elaborates | rewritten-crate model (probe crate) | yes | unchanged |
| `full_round` | state_only_poseidon.rs | translates; elaborates (failed only through its callee external_linear_lazy) | settled | yes | unchanged |
| `full_round_m31_constants` | state_only_poseidon.rs | translates; elaborates (failed only through its callee external_linear_lazy) | settled | yes | unchanged |
| `full_round_m31_constants_packed` | state_only_poseidon.rs | translates; elaborates (callee external_linear_lazy) | rewritten-crate model (probe crate) | yes | unchanged |
| `full_round_packed` | state_only_poseidon.rs | translates; elaborates (callee external_linear_lazy) | rewritten-crate model (probe crate) | yes | unchanged |
| `internal_linear_lazy` | state_only_poseidon.rs | translates; elaborates | rewritten-crate model (probe crate) | yes | unchanged |
| `internal_round` | state_only_poseidon.rs | translates; elaborates | rewritten-crate model (probe crate) | yes | unchanged |
| `interpolate_three_constant_columns` | state_only_poseidon.rs | translates; elaborates | settled | yes | unchanged |
| `interpolate_three_constant_limb` | state_only_poseidon.rs | translates; elaborates | settled | yes | unchanged |
| `interpolated_full_pair_packed` | state_only_poseidon.rs | translates; elaborates | rewritten-crate model (probe crate) | yes | unchanged |
| `interpolated_internal_pair` | state_only_poseidon.rs | translates; elaborates | rewritten-crate model (probe crate) | yes | unchanged |
| `leading_pair_packed` | state_only_poseidon.rs | translates; elaborates (callee external_linear_lazy) | rewritten-crate model (probe crate) | yes | unchanged |
| `pow5` | state_only_poseidon.rs | translates; elaborates | rewritten-crate model (probe crate) | yes | unchanged |

Every function whose R1 row is SETTLED shows "yes" in the identity column. None of them failed
in my run, so there is no contradiction to report. `full_round` and `full_round_m31_constants`
(SETTLED, with `external_linear_lazy` bound by name to the probe constant) are unchanged, and the
callee they bind to now has the probe crate's text.

## 3. Rewrites

Rules held for every rewrite: same value on every input; no `unsafe`; no new feature flag; index
loops with straight-line bodies; no `return`, `?` or `break` in a loop; no `iter_mut().rev()`; no
closure capturing mutable state. The old form is kept verbatim in a `#[cfg(test)]` module and
tested against the new one. Each rewritten function is compiled into the prover too.

| Function | Change | R1 text adopted? | Operators, effect order, error precedence | Same under the client feature set? |
|---|---|---|---|---|
| `state_only_poseidon::external_linear_lazy` | inner `while output` loop replaced by four calls of the new `#[inline(always)] external_linear_lazy_row`; its own `from_fn` and the two `from_fn` sites of `sums` and the final loop written as `crate::array_from_fn_copy`; `array_from_fn_copy` added to `lib.rs` | yes, verbatim: helper name, body and the three call sites from `input/src/statement/state_only_poseidon.rs` (lines 142-195) and the `lib.rs` hunk of `actual-merged-input.patch`, both under `docs/research/100bit-spend-path-20261013/evidence/terminal-qm31-extraction-20261016/attempt-fromfn-copy-indexed/` on origin/research (the text of R1's `RPu_FIq_Native06`). Only `crate::` now resolves to `aspis_statement` | unchanged: the same `u64` `+`/`*` expressions in the same order (row 0 limbs 0..3, then row 1, ...; then the sums, then the final pass); the function cannot fail except by arithmetic overflow, which the operators decide exactly as before | yes: no `cfg` in or around it |
| `pair_forest_copy_terminal::pattern_values_windowed` | the local closure `window` became the function `pattern_window(prepared, openings, start)` with the same body | no R1 model exists (deployed audit kernel); smallest change | unchanged; pure function, no failure path besides indexing, which reads the same indices | yes: the helper carries the caller's `cfg(any(test, feature = "pool-v1-pair-forest-pattern-window-audit"))` |
| `pair_forest_semantic_terminal::composition_parts` | the two Horner loops `for lane in x.into_iter().rev()` became `for index in (0..x.len()).rev()` reading `x[index]`; the withdrawal-amount guard moved unchanged into `fn invalid_withdrawal_amount(Option<u32>) -> bool` | loops: yes, the probe crate's text for exactly these two loops (`actual-merged-input.patch`, same evidence directory); the guard: the probe crate had an older `is_some_and` form, so no text to adopt; smallest change | unchanged: the same multiply-add sequence in the same order; the amount check still runs first and returns `InvalidPublicAmount` before `validate_transition` can return `InvalidAppendTransition` (tested with both failing together) | yes: no `cfg` in the changed lines |

Why `composition_parts` is changed in the source and not by a library addition:
- The Horner loops: the R1 model of this function already has the index form, so adopting that
  text keeps a fresh emission in R1's shape. A library addition (`fold`/`rev` fields of the array
  iterator) would also have worked for this construct.
- The guard: the failure is not a missing library model. It is an ill-typed emitted term: Aeneas
  binds the `||` value through a `let b ← if … then ok true else … ok (amount >= i)`, and Lean 4.32
  types `b` as `Prop`. No library item covers that. With the guard in a function whose result type
  is `bool`, the emitted Lean elaborates (T2-L07b).

Library additions, not source changes:
- `reconstruct_10` (slice-iterator `next_back`). The Rust is ordinary and its R1 model has the same
  `.iter().rev().fold` text.
- `Public::terminal_qm31` (`Result::map`).
- Both definitions are copied from the Aeneas library beside the second pair's binary into the test
  shim `translatability/statement/AspisTP2NewLib.lean`. They are each a library row to record, not
  Aspis code.
- I had first rewritten `reconstruct_10` and the two `fold`s of
  `evaluate_state_only_poseidon_oracle_projected` as index loops. Following the coordinator's
  ruling, I reverted both before any gate. The projected oracle elaborates as found, with std
  axioms.

## 4. Batches and gates

Gate script: `fv_sampler_gate.sh <name> src-tp2-<name> src-base2 BASE2=…`, then
`fv_gate_compare.py <name> BASE2`. Budget rule of the coordinator: up to 300 CU per function, 1,500
for the pass.

Batch `tp2-b1`: `external_linear_lazy` and `pattern_values_windowed`.
- Patch `translatability/statement/tp2-b1.patch`, sha256
  2625fc8cfa11f93b4060a3bf540e2f894016adb0e05e0a2374167256c410a0fa.
- Gate status OK. The mutation verdict files are identical: 156,706 lines, both sha256
  e3659a53d3b4e308711668d82715cd981e8d3bdc7ba859c9ff3bdaa1e3c9e2b9.
- Prover output (pinned and re-packed proof hashes) is identical to the unchanged tree in all six
  worst-case scenarios.
- All replay conditions hold, and the redirect run exited 0.
- Compute: transfer 1,281,023 against BASE2 1,280,964, and withdrawal 1,287,544 against 1,287,485,
  so +59 on both payments. The worst case is +59 in every scenario and variant.
- Split: a build with only `external_linear_lazy` changed (`tp2-s2`, round-7 build and replays
  only) costs +102 on both payments. By difference, `pattern_values_windowed` saves about 43. That
  half was not measured alone.
- ELF sha256 fdf0733fe33d58d2694e29ca144cf432714f23b990142c3d36e485af7d254164.
- Crate tests: 31 passed (T2-U01), including the two oracles: 200,000 random states plus edge
  values, including non-canonical limbs, for `external_linear_lazy`, and 120,000 for
  `pattern_values_windowed`.

Batch `tp2-b2c` (cumulative: tp2-b1 plus `composition_parts`).
- Patch `translatability/statement/tp2-b2c.patch`, sha256
  b204855fe484a2b27e373144e035a66cdf4071549460711010c74063ac544d48.
- Gate status OK. The mutation verdict files are identical (both sha256
  e3659a53d3b4e308711668d82715cd981e8d3bdc7ba859c9ff3bdaa1e3c9e2b9).
- Prover output is identical to the unchanged tree in all six scenarios.
- All replay conditions hold, and the redirect run exited 0.
- Compute: transfer 1,280,857 against BASE2 1,280,964 (-107), and withdrawal 1,287,377 against
  1,287,485 (-108). The worst-case scenarios are -108 for withdrawals and -107 for the transfer, in
  every variant.
- Against tp2-b1, the `composition_parts` change saves 166 on transfer and 167 on withdrawal.
- The whole pass is therefore below the base. Per function: `external_linear_lazy` +102 (measured
  alone); `pattern_values_windowed` about -43 (by difference); `composition_parts` -166/-167 (by
  difference from tp2-b1).
- ELF sha256 11cb36c7d56645fa01b74b6c8a8ebb60ae911a18e2e9680d475048702f4032dd.
- Crate tests, deployed features: 33 passed (T2-U03). This includes `composition_parts` old
  against new on 100,000 random claim sets: transfer and withdrawal, half at Boolean points, plus a
  failing transition and every amount edge (0, 1, 2^30-1, 2^30, u32::MAX) alone and with the
  failing transition. It also includes the guard helper against the pinned expression on 200,000
  values and the edges.
- Crate tests with only `r0,pool-v1-kernel` (the other `cfg` branch): 33 passed (T2-U04), the same
  four oracle tests included.

## 5. Release-style emission of the rewritten scope (tree `src-tp2-b2c`)

Charon:
- T2-C07, exit 0, 57 s, peak RSS 0.66 GiB.
- LLBC sha256 29c7793ca9422e2ae030a050d39a3e3b3a084b02e2753fd801a07d0d2a218ce5.

Aeneas, second pair, WITH `-abort-on-error`:
- T2-A07, exit 0, 104 s, peak RSS 0.97 GiB.
- Funs.lean sha256 4b656a0b0fee8bfe84a18bfe9031dcefb94f643c71ac7e641809d6a50ecf8eb2.
- Types.lean sha256 35ff2a9711a27dbb9cd04815f36a35f112b8a308a1a4b559f4751b28fc897909.
- FunsExternal_Template sha256 0f9bd4c2541e1b406bd7de49332d44fc4fac4293f4f9376ed84d34e610852335.
- The batch-1 tree's emission with the flag (T2-A04) also exited 0.

Lean:
- TypesExternal, Types and FunsExternal exit 0 (T2-L07-*).
- Funs exits 0 with no error and no `sorry` (T2-L07b-Funs, 66 s, scope peak 0.84 GiB). This uses
  the probe's adaptation and shim plus `AspisTP2NewLib`
  (sha256 0d47d5e3a7d4f5b699e820567bffdb424fb8866985c6da442beb9aac8e138344, which compiled as
  T2-L00b), via the rules file `XP_rules_tp2.json`.
- The first Funs compile (T2-L07-Funs, exit 1) ran before the shim object existed and is not
  relied on.
- Every Aspis declaration of the emission elaborates. The remaining std items are axioms of the
  external template, each a library row: `Array` `into_iter`, array `IntoIter` `fold`,
  `core::array::map`, `Rev` `fold`, `Iterator::fold` default, `RangeInclusive` `fold`, `Range`
  `clone`, `Option` `eq`, slice `Iter` `fold`.

Completeness against Charon's declaration list (`fv_tp2_release_checks.sh`, output in
`tp2/release-checks-T2-A07.txt` on the host). 274 structured `aspis_statement`/`aspis_core`
declarations; 25 have no definition in the emission:
- 13 derived `Clone::clone` methods of `Copy` types (10 in `aspis_statement`, 3 in `aspis_core`).
- The `call_mut`/`call_once` methods of six `Fn` closures or function items, whose `call` is
  emitted: `equality_value`'s closure, and in `aspis_core::field` `mul`, `new`, `square`,
  `qm31_pack_base4` and `qm31_from_karatsuba_channel_sums`.
- No emitted definition refers to any of them, since the Lean elaborates with no unknown
  identifier.
- `PreparedQm31Multiplier::mul`, which the probe found silently missing (finding 2), IS emitted
  here (Funs.lean line 558).
- The omissions are the silent class the probe named, and their cause is not established. They
  are recorded, not resolved.

Erased-region scan of the LLBC:
- No mutable-borrow type argument (inside `generics`) has an erased region.
- 34 mutable references with erased regions occur only as local or operand types in bodies, which
  is ordinary LLBC.
- There is no `iter_mut().rev()` in the scope.

## 6. Boundaries relied on (other workers' scopes)

- `aspis_core::field`: the QM31/CM31/M31 kernels, `PreparedQm31Multiplier`, `qm31_pack_base4`, the
  `qm31_sum_products*` and `qm31_m31_dot`. They were translated in my emission and are the core
  worker's text.
- `aspis_core::state_only_hiding::state_only_selected_mask_value`.
- `aspis_core::state_only_prefix::r0::{Challenges, Error, PointClaims}`.
- `aspis_core::field::wide_exact`, opaque.
- The statement-record types and constants of `pair_tree_profile`, `payment_relation` and
  `pair_terminal`.
- The decoders that produce the `Public` value (`decode_pool_v1_pair_forest_terminal_statement_v1`
  and its callees) are the decoder worker's.

## 7. What remains

- `external_linear_lazy`, `pattern_values_windowed` and `composition_parts` now translate and
  elaborate. Equality of the new text with R1's gates is not attempted here. For
  `external_linear_lazy` the text is the probe's, so the soundness lead's by-name binding can now
  be a text comparison.
- Library rows to record:
  - `core::result::Result::map`;
  - `core::slice::iter::Iter` `next_back`;
  - the nine std axioms of section 5.
- The deployed audit kernels have no R1 model. They are listed as "no model" in section 2, and for
  each, equality with its unoptimised kernel is owed. These kernels are the `*_factored`,
  `*_selector_tensor*` and copy-basis kernels, `add_preweighted_shared_selector`,
  `pattern_values_windowed` and `active_mask_basis`.
- The 25 silently absent declarations of section 5 are unexplained. They are unreferenced in this
  emission.
- No proof of anything here; no source-to-model refinement.
