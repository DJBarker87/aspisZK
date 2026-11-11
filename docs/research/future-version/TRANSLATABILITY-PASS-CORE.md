# Aspis translatability pass: aspis-core and the statement decoders (worker 3)

Status: target not yet established. This note records which functions of `crates/aspis-core` and of the
statement and account decoders in `crates/aspis-statement` that the deployed Aspis verifier program reaches
the translator accepts, which it rejects, what was reshaped and how the reshaping was tested. Everything
here is a tool run or a test. Nothing is proved, and a translated function is not a verified function.

Source: the head's source (`7dffe3e2a93`, host copy `src-tp3-base`, every file of the four crates checked
equal to `git archive 7dffe3e2a93`), and from batch 1 on `src-base2`, which differs from it only in
`aspis-r1-cost-probe` (`fused.rs`, `multiproof.rs`, `sampler.rs`). Neither crate of this note differs between
the two. Against the R1 pin `c7593d23fdc`, `crates/aspis-statement` is byte-identical, and `crates/aspis-core`
differs in `Cargo.toml` (four feature lines), `digest.rs` (`Digest32::digest_into`, new) and `field.rs`
(`PreparedQm31Multiplier::mul`, `QM31::mul`, `QM31::square` gained a `#[cfg(feature)]` fast branch,
`QM31::mul_add` is new, plus a test module). Every other function of either crate is text-identical to the
pin.

## 1. Method

Tool pair: the second pair of the extraction probe (Charon 454586e9, sha256
`57aa2359bb3e9a84480f7e4802dcdc700ef05709de30ec0eb97581b3f9c5f851`; Aeneas 0d21a9ec, sha256
`230ee9f0c4902ea3415a01960f6887e2d4c71bc82e8b4e78dfac398da657df91`; nightly-2026-09-17), with the probe's
command line and environment (`XP_charon.py`, `XP_aeneas.py`, copied unchanged except that they also accept
the crates `statement` and `core`), overflow checks on. It is the pair of R1's PIN2 re-extractions and the
stronger of the two on loops. The first pair (Charon daad69be, Aeneas b59d5188-extended) was run only on the
two settled functions the second pair rejects for a function-pointer argument (section 3). The privacy lead's
combined translator was not used for emissions: it belongs to the first pair's lineage. Its check for the
dropped-write shape was replaced by a structural LLBC scan (section 6).

Feature sets, exactly those the deployed verifier build gives these crates (`fv_round7.sh`, both
`Cargo.toml` files): aspis-core `r0,future-fast-kmul,future-fast-prepared,future-fast-square,future-lazy-horner`;
aspis-statement `r0,pool-v1-kernel` plus the nine `optimized-terminal` audit features
(`pool-v1-pair-forest-packed-digest-selector-tensor-audit, -binary-copy-weights-audit,
-endpoint-selector-cache-audit, -semantic-factor-audit, -pattern-window-audit, -copy-tag-dot-basis-audit,
-copy-finish-dot-basis-audit, -packed-range-audit, -active-mask-basis-audit`). Each crate was emitted as its
own (local) crate; section 4 shows why that matters.

Reachability: Charon on the program crate from `process_r1_cost_probe_instruction`, with the deployed program
features and the three Aspis crates transparent (`T3-C04`, LLBC sha256
`9aef588a218e449264d846511de22d073a4dd2ce76f6fca8b2b01fefea696fb3`, 1,518 functions). Charon follows the
code as compiled, `cfg` evaluated, so a function absent from that list is not linked into the deployed
program; a function present may still be unreachable at run time (column "path" below says which).

Runs (receipts under `~/project-offloads/future-version-20261111/receipts/`, all through `fv_slot.sh`, 6G/8G,
no swap; none killed): `T3-C04` reachability (7 s, 0.54 GB scope peak); `T3-C05`/`T3-A05` statement
(Charon 68 s 0.74 GB; Aeneas 73 s, 4.04 GB scope peak, the largest figure of this pass); `T3-C06`/`T3-A06`
core (21 s 0.71 GB; 19 s 0.27 GB); Lean `T3-L05-*`, `T3-L06-*` (Lean 4.32.0 against the L187 objects with the
probe's two adaptations: module headers and the `AspisXPNewLib` shim; `fv_tp3_lean.sh`). Two earlier runs
were inputs of mine that failed, not tool limits: `T3-A02` (Aeneas crashed on `Public` because I had made the
semantic-terminal module opaque, which also made its types opaque) and `T3-A03` (core run over whole modules;
Aeneas stopped with an internal error on an iterator signature in code the program does not reach).

## 2. Classification (deployed features, second pair, before any rewrite)

Columns: path = on the deployed verifier's run-time path (yes), linked but not reachable at run time (linked),
or not linked; R1 row = status of the row in the soundness lead's table (settled / translatable as is /
rewrite needed / rewritten-crate model / hand model / no model), read with the correction of 2026-11-11 that a
row marked non-frozen, detector-blind, ReviewedTranscription or OPEN_TRANSCRIPTION counts as a rewrite
candidate unless SETTLED; pin = text identical to `c7593d23fdc`.

"Linked" functions are reached only through `lifecycle_finalize` (`validate_lifecycle_final_body` decodes a
full ASF8 statement) and `stage1`. `pool_route::admitted` rejects tags 4, 5 and 6 before dispatch, and with
`future-one-tx-lean` `stage1` returns an error before reading anything, so at run time neither is entered. The
full ASF8 decoder is still in the immutable program, so it is classified like the rest.

### 2.1 Statement and account decoders

| Function | path | Translates | Lean | R1 row | pin |
|---|---|---|---|---|---|
| `decode_pool_v1_pair_forest_terminal_request_v1` | yes | yes | elaborates | no row | yes |
| `encode_pool_v1_pair_forest_terminal_request_v1` | not linked (Pool only) | yes | elaborates | no row | yes |
| `PoolV1PairForestTerminalPaymentV1::nullifier`, `...StatementV1::{common, transition_kind, nullifier, semantic_public}` | yes | yes | elaborate | translatable / no model | yes |
| `pool_v1_pair_forest_output_lane_v1`, `digest_is_canonical`, `first_canonical_byte` | yes | yes | elaborate | translatable as is (non-frozen) | yes |
| `validate_pool_v1_pair_forest_terminal_statement_v1`, `statement_public_common`, `transition_kind` | yes | yes | elaborate | translatable as is | yes |
| `validate_result`, `validate_..._result_against_statement_v1`, `encode_..._result_v1` | yes | yes | elaborate | no model | yes |
| `decode_pool_v1_pair_forest_master_v1` | yes | **no**: "Could not match the contexts" (pair_forest_accounts.rs 295:4-298:5, the `iter_mut().enumerate()` loop) | none | rewrite needed (CE15) | yes |
| `validate_master` | yes | yes | **no**: `any` is not a field of the library's `Iterator` (the `.iter().any(..)` closure) | rewrite needed | yes |
| `decode_pool_v1_pair_forest_checkpoint_v1` | yes | **no**: "Could not match the contexts" (463:4-482:1, the `iter_mut()` loop with a `return`) | none | rewrite needed (CE15) | yes |
| `decode_pool_identity_v1`, `decode_verifier_policy_v1`, `validate_verifier_policy_v1` | yes | yes | elaborate | hand model / rewrite candidate (CE15 callee) | yes |
| `decode_pool_v1_pair_verified_afterstate_v1` | yes (`scan_proof_buffer`) | yes (29.5 s) | **no**: parse error at the 20th nested `?` ("unexpected identifier; expected '=>'"), the twenty unrolled frontier reads | rewrite needed (CANNOT_EXTRACT key) | yes |
| `encode_pool_v1_pair_verified_afterstate_v1`, `validate_verified_afterstate`, `exact` | yes | yes | elaborate | settled / translatable | yes |
| `decode_digest_canonical`, `encode_digest_canonical`, `unwrap_fixed_slice` | yes | yes | elaborate | translatable as is (non-frozen) | yes |
| `decode_verifier_registry_{v1,v2}`, `decode_verifier_registry_entry_{v1,v2}`, their `validate_*`, `is_paused`, `is_immutable`, `is_active_at`, `has_no_retirement_slot`, `required_binding_is_zero`, `TryFrom<u8>` | yes | yes | elaborate | hand model (NJY-RT201/203) | yes |
| `decode_pool_v1_pair_forest_terminal_statement_v1` (CE17, a timeout under 959659a6) | linked | yes (0.3 s) | elaborates | rewrite needed (CE17) | yes |
| `decode_terminal_common_boxed_v1`, `decode_lane_transition_boxed_v1`, `decode_transfer_statement_boxed_v1`, `decode_withdrawal_statement_boxed_v1` | linked | yes | elaborate | rewrite needed (CANNOT_EXTRACT keys) | yes |
| `decode_pool_v1_pair_late_public_statement_boxed_v1`, `decode_pair_live_snapshot_boxed_v1`, `decode_pair_afterstate_boxed_v1` | linked | yes | elaborate | rewrite needed | yes |
| `decode_pool_v1_pair_live_snapshot_v1` | linked | yes (14 s) | **no**: type mismatches at the deepest of the twenty nested `?` | rewrite needed | yes |
| `validate_pool_v1_pair_live_snapshot_v1`, `encode_pool_v1_pair_live_snapshot_v1`, `encode_..._late_public_statement_v1` | linked | yes | elaborate | settled / translatable | yes |
| `encode_pool_v1_pair_forest_terminal_statement_v1` | not linked in the one-transaction build | **no**: "Could not match the contexts" (pair_forest_terminal.rs 318:18-324:9) | none | (op22) | yes |

So for this crate the translator verdicts differ from R1's table in both directions: CE17 and the boxed family
translate and elaborate as written under the second pair (R1's failures were a timeout and a crash of the
first-pair tools), while the master and checkpoint decoders, `validate_master`, and the two twenty-digest
frontier decoders fail.

Boundaries relied on (other workers' code, opaque in these runs): `decode_pool_v1_private_transfer_public_v1`,
`decode_pool_v1_withdrawal_public_v1`, `encode_pool_v1_private_transfer_public_v1`,
`encode_pool_v1_withdrawal_public_v1` (payment relation); the `Public` type of the semantic terminal (its
functions are not called by any decoder). Not part of the verifier path and not touched: the lane-state codec
and `IncrementalMerkleTreeV1` (the adapter decodes the lane with its own `decode_lane_from_pool_release`).

### 2.2 aspis-core

| Function (deployed branch) | path | Translates | Lean | R1 row | pin |
|---|---|---|---|---|---|
| `QM31::mul` sixteen-product (`future-fast-kmul`) | yes | yes | elaborates | no R1 model; equality with the plain kernel owed | no |
| `QM31::square` (`future-fast-square`) | yes | yes | elaborates | no R1 model; equality owed | no |
| `QM31::mul_add` (`future-lazy-horner`) | yes | yes | elaborates | no R1 model (new); equality owed | no |
| `PreparedQm31Multiplier::mul` (`future-fast-prepared`) | yes | yes | elaborates | no R1 model for this branch; equality owed | no |
| `CM31::mul` | yes | yes | elaborates | settled | yes |
| `Digest32::digest_into` (default method) | yes | yes | elaborates | no model (new) | no |
| M31, CM31, QM31 `add`, `sub`, `neg`, `double`, `mul_m31`, `from_m31`, `from_cm31`, `is_zero`, `from_le_bytes`, `to_le_bytes`, `ZERO`, `ONE`, `reduce_u62`, `reduce_u64`, `pow`, `inv` (M31), `try_inv`, `square_n`, `reduce_u64`, `mul_by_r`, `CM31::square`, `PreparedQm31Multiplier::new` | yes | yes | elaborate | settled, or translatable as is | yes |
| `CM31::new` | yes | yes | elaborates | rewritten-crate model (Post25) | yes |
| `CM31::inv` | yes | **no**: "Invalid input for unop: fn_def_to_fn_ptr" (field.rs 391) | none | **settled** | yes |
| `CM31::inv_with` | yes | **no**: "Arrow types are not supported yet" (field.rs 396-403) | none | **settled** | yes |
| `qm31_from_karatsuba_channel_sums`, `qm31_accumulate_product_channels`, `qm31_sum_products_small`, `qm31_sum_products{2,3,4}`, `qm31_sum_products3_prepared`, `qm31_pack_base4`, `qm31_m31_dot` | yes (semantic terminal) | yes | elaborate | settled, ReviewedTranscription or probe-crate | yes |
| `WideExact::new`, `canonical_qm31`, `c0`, `c1`, `from_qm31`, `add`, `sub`, `neg`, `mul`, `mul_u`, `mul_qm31`, `mul_m31`, `from_limbs`, `to_limbs`, `from_le_bytes` | yes | yes | elaborate | settled / rewritten-crate model (`new`) / no key | yes |
| `WideExact::to_le_bytes` | yes (`fused::claims_bytes`, transcript input) | yes | **no**: the `chunks_exact_mut(4).zip(..)` loop needs `Iterator` fields (`zip`, `rev`) and a `ChunksExactMut` instance the library lacks | DEPENDS_ON_LIBRARY_TRUST, not settled: rewrite candidate | yes |
| `r0::heap::filled` | yes | yes | **no**: unknown `alloc.alloc.Global` (library naming of `try_reserve_exact`) | rewritten-crate model (ClaimsUnrolledParentSource), not settled | yes |
| `r0::heap::uninit` | yes (verifier `claims`) | **no**: "Raw ptr casts are only supported between pointers to literal types" | none | rewrite needed (unsafe) | yes |
| `r0_transcript::queries_from_pairs`, `QueryScan::{default, scan, finish}`, `block_rank`, `query_words` | yes | yes | elaborate | hand model (OPEN_TRANSCRIPTION) | yes |
| `r0_transcript::base_p_digits` (`iter_mut().rev()`) | **not linked** (absent from T3-C04; the verifier crate uses its own sampler) | not run | | | yes |
| `r0::domain` (`FibreIndex::{new,get}`), `r0::scalar` impls | yes | yes | elaborate | | yes |
| `state_only_hiding::{state_only_selected_mask_value, selected_mask_linears, mul_tower_basis, mask_power_26, cm31_mul_i, cm31_mul_r}` | yes | yes | elaborate | settled (probe-crate) | yes |
| `state_only_prefix::{r0::statement_points, state_only_statement_points}` | yes | yes | elaborate | settled | yes |
| `state_only_private_merkle::private_leaf_hash_with_digest` | yes | yes | elaborates | no key | yes |
| `transcript::circle_fallback_point`, `circle::{secure_circle_point_from_parameter, secure_ood_circle_point_from_parameter}` | yes | yes | elaborate | settled / translatable | yes |
| `r0::opening::inactive`, `r0::merkle::parent_with_digest` and the rest of `r0::merkle` (only `C1_TAG`, `C2_TAG` are reached) | not linked | not run | | | yes |

`CM31::new` and `WideExact::new` (column (b) of R1's table: rewritten-crate model, Post25): the model text
(`AspisR1Post25Sampler.Funs`, prover-commit25 extraction) has the same shape as the shipped functions
(`ok { a, b }`; `canonical_qm31` of each half). The difference is the crate the model was emitted from, not the
function text, and the shipped functions translate and elaborate as they are. No rewrite was made; the link is a
fresh emission of the shipped crate, which this pass provides (section 7).

## 3. Settled functions the second pair rejects (not rewritten)

`CM31::inv` and `CM31::inv_with` are SETTLED in R1's table. Their gates are first-pair emissions (AspisR72Sampler),
and the soundness lead ruled that they carry over to Aspis by text identity. The second pair rejects both: `inv`
with "Invalid input for unop: fn_def_to_fn_ptr on aspis_core::field::{aspis_core::field::M31}::inv" (field.rs
391) and `inv_with` with "Arrow types are not supported yet" (field.rs 396-403), because `inv_with` takes
`inverse: fn(M31) -> M31`. The first pair (Charon daad69be, Aeneas b59d5188-extended) translates both
(`T3-C10`/`T3-A10`, exit 0), and that emission elaborates (`T3-L10`, exit 0). Record: settled; first-pair gate;
the second pair rejects (fn_def_to_fn_ptr / arrow types). Both are untouched and text-identical to the pin.

## 4. Cause of the silent omission of `PreparedQm31Multiplier::mul` and `CM31::mul`

Reproduced (`T3-C07`/`T3-A07`): Charon on the verifier crate with the four field `mul` functions as roots and
`aspis_core::field` included puts all four (and `WideExact::mul`) in the LLBC; Aeneas, exit 0 and no message,
emits only `M31::mul` and `QM31::mul`. With aspis-core emitted as the local crate (`T3-A06`) all of them are
emitted.

Cause, read in the Aeneas source shipped beside the second pair's binary (`aeneas-exact-source.tar.gz`,
`src/PrePasses.ml`, function `simplify_trait_calls`, from line 1783): after simplifying trait calls the pass
recomputes the set of used functions. It starts from every LOCAL function and from the bodies of all functions,
and then keeps only the declaration groups whose function is in that set. A function of another crate that no
translated body calls is dropped from the declaration groups, with no message. In the probe aspis-core was a
dependency of the crate being translated, and under the deployed features nothing in that scope calls
`CM31::mul` (the sixteen-product `QM31::mul` no longer does) or `PreparedQm31Multiplier::mul` (its callers are
in the semantic terminal, outside the probe's scope). They were dropped although they are roots.

Consequence: emit aspis-core as its own crate, and check every release emission for completeness against
Charon's list (section 6). The completeness check also finds a second silent class in the local-crate
emission: the derived `Clone::clone` of eight `Copy` types (`M31`, `CM31`, `PreparedQm31Multiplier`,
`WideExact`, two circle types, `r0` and `transcript` types) and one derived `PartialEq::eq` are not emitted and
no error is given; no emitted body calls them.

## 5. Rewrites

Two patch series, made with `diff -ruN` against `src-base2` and restricted to one crate each, in
`docs/research/future-version/translatability/core/` (sha256 in section 8). Every rewritten function keeps its
old text verbatim in a `#[cfg(test)] mod translatability_oracle` beside it, and is tested against it there.
Neither crate gains `unsafe`, a feature flag or a closure that captures mutable state. Every new loop is an
index `while` loop with a straight-line body; a `return` or `?` appears only in a loop that nothing but the
result follows.

### 5.1 Decoders (`tp3-dec2`; `tp3-dec1` was the same code with the helpers placed earlier in the files)

| Function | Change | Operators, effect order, error precedence |
|---|---|---|
| `validate_master` | `last_checkpoint_lane_sequences.iter().any(|s| *s > CAP)` becomes `any_lane_sequence_above_capacity(&..)` (index loop, early `true`) | unchanged: the same comparison, the same four checks in the same order, the same error for each |
| `decode_pool_v1_pair_forest_master_v1` | `bytes[50..64].iter().any(..)` becomes `any_nonzero_byte(&bytes[50..64])` (still the left operand of the same `||`); the `iter_mut().enumerate()` fill becomes `lane_sequences_at(bytes, 320)` | unchanged: no arithmetic changed (`MASTER_LAST_SEQUENCES_OFFSET + 8 * lane` as before), every check in the same order, the reads are infallible after the length check |
| `decode_pool_v1_pair_forest_checkpoint_v1` | `bytes[176..].iter().any(..)` becomes `any_nonzero_byte(..)`; the `iter_mut()` loop that read each lane sequence and returned `InvalidMasterState` on the first one above capacity becomes `lane_sequences_at` followed by `any_lane_sequence_above_capacity` | error precedence unchanged: every lane failure is the same `InvalidMasterState`, the reads cannot fail, and no other check sits between them; operators unchanged |
| `decode_pool_v1_pair_verified_afterstate_v1` | the twenty unrolled `decode_digest_canonical(&exact(..)?).map_err(..)?` become `decode_afterstate_frontier_v1(bytes)?` (index loop over the levels, same two `?` per level) | unchanged: root first, then levels 0 to 19, then `next_pair_index`, then `validate_verified_afterstate`; the first non-canonical digest gives `NonCanonicalAfterstate` as before; `48 + 32 * level` gives the same offsets |
| `decode_pool_v1_pair_live_snapshot_v1` (linked, not run) | the same change, `decode_live_snapshot_frontier_v1` | as above (`NonCanonicalDigest`) |

The verbatim old texts compile in the oracle modules with one change: in `pair_terminal.rs` the constant
`super::POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION` is written `super::super::..` because the copy sits one module
deeper.

Prover and client: these decoders are compiled into the prover and client too. The new code has no
`cfg`, so it is the same under the client and the deployed feature sets.

### 5.2 Core (`tp3-core1`)

| Function | Change | Operators, effect order, error precedence |
|---|---|---|
| `WideExact::to_le_bytes` | `for (chunk, limb) in bytes.chunks_exact_mut(4).zip(self.to_limbs())` becomes an index loop writing `bytes[4*i..4*i+4]` from `limbs[i].to_le_bytes()` | unchanged: the same bytes in the same order; no fallible step; `4 * index` cannot overflow; no `cfg`, so the same under the client and the deployed feature sets |

Not rewritten, with the reason:
- `r0::heap::uninit`: `unsafe` raw-pointer allocation. The only safe stable replacement, `Box::new_uninit()`,
  aborts on allocation failure where `uninit` returns `Error::Allocation`. That changes an error path, so the
  function is left as it is and stays a named gap (an opaque function with a stated specification, or a
  translator change).
- `r0::heap::filled`: its Lean fails only on the library's name for the global allocator. The rewritten-crate
  model R1 uses has the same source text, so no source change helps. This is a library-row matter.
- `CM31::inv`, `CM31::inv_with`: settled first-pair gates; see section 3.
- The four fast kernels translate and elaborate as they are. Their equality with the plain kernels is owed
  (tested in `future_fast_kmul_tests`, not proved).

## 6. Gates, per batch

Gate scripts as briefed: `fv_sampler_gate.sh <name> src-tp3-<name> src-base2 BASE2=...` and
`fv_gate_compare.py <name> BASE2`; Pool check `fv_tp3_pool.sh` (wraps the fourth worker's `fv_pool_build.sh`,
`fv_pool_test.sh` and `fv_pool_replay.sh`, read-only use); crate tests `fv_tp3_tests.sh`. The baseline Pool
ELF `out/PL-base` (sha256 `e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc`) was built from
Pool, core and statement sources equal to `src-base2` (its `source_files.sha256` matches file for file).

| Batch | Patch sha256 | Verifier ELF | Recorded payments (CU vs BASE2) | Worst case, 6 scenarios x 3 variants | Mutants (156,706) | Prover output | Replay and redirect conditions | Pool ELF | Pool's own cost | Own tests |
|---|---|---|---|---|---|---|---|---|---|---|
| tp3-dec2 | `2285fd6b03e5443ae06e171603bd6622986cb13bc1fe1a3287ebb41f595ff444` | `5168d921a35210d3edc9a8235e6d1a77ca47035bb7c0fad41c4c8dbb5eac7cea` | transfer 1,281,271 (+307), withdrawal 1,287,792 (+307) | +307 in every cell | verdict files identical | identical in all 6 | all hold; redirect exit 0 | changed: `c88dc527c9881da8774694c0d8c6f54a1fc8b1c6e91a93d493535ffac64ce0bf` | +307 on both payments (control 1,140,179 vs recorded 1,139,872; 1,155,737 vs 1,155,430); all Pool replay conditions hold; Pool tests 67 + 36 pass | statement 265 passed, 1 failed (the stale format test, section 9) |
| tp3-core1 | `bb4d54aa559e9decc4a37979648b40e5a0324bc3b33e71fa1987c0f5f2bf8f2c` | byte-identical to BASE2: `7540abe6c5f07827011b11d3313fe5594816a32fa05963195ee4a1f5cf7856b5` | 0, 0 | 0 in every cell | identical | identical in all 6 | all hold; redirect exit 0 | unchanged | 0 | core 282 passed, 1 ignored |

The +307 of tp3-dec2 is one batch figure over four on-path decoders (master, checkpoint, `validate_master`,
verified afterstate). It was not split, under the budget rule of 2026-11-11 (300 per function, 2,000 for the
pass). The likely source is the zero-initialised 640-byte frontier array that the loop fills, where the unrolled
form built the array in place. That is a reading, not a measurement. tp3-dec1 (the same code, helpers placed
earlier) gave the same Pool ELF hash and the same +307. Its verifier gate was stopped before it started and
replaced by tp3-dec2.

Pass total: verifier +307, Pool's own cost +307.

### Pool-linked functions changed (tp3-dec2)

Old lines are at `src-base2` (equal to the pin for this crate), new lines with the patch applied. Body hash =
sha256 of the function's lines including its attributes (`translatability/core/tp3_fnranges.py`,
run on the two trees).

| File | Function | Old lines | Old body sha256 | New lines | New body sha256 |
|---|---|---|---|---|---|
| pair_forest_accounts.rs | `validate_master` | 204-231 | `2b722ee67a4e1f01910341c5c8d5a2cf48bb66f6f787416e07dc1394615d67e0` | 204-227 | `915516536978d21672b41f5a4dcd3fe3b227ade8c28a4d2e82c0f5164bd001f5` |
| pair_forest_accounts.rs | `decode_pool_v1_pair_forest_master_v1` | 261-314 | `8b34e2faaf3deafe2523a694212a8a0223f7346f651cf0cb5d54b0335ac6ba36` | 257-306 | `c921a82fabb5691d36ec1b4779a83267574d69c573ed9637beda49b1784c0acb` |
| pair_forest_accounts.rs | `decode_pool_v1_pair_forest_checkpoint_v1` | 426-482 | `49ec3adb69fcf276311576d9ed34d1db6a64cfdcca9612ff5397b5bbe2b2d82d` | 418-470 | `fa3359d70cee9a91ecf27e40adf607a686a00411056990cad7316ea1267f1b16` |
| pair_forest_accounts.rs | `any_nonzero_byte` (new) | - | - | 543-553 | `55c3b34fe6fdc174e27c06b717776524e7be5410281d2c7f6b8368fda03b93fc` |
| pair_forest_accounts.rs | `any_lane_sequence_above_capacity` (new) | - | - | 555-567 | `b6ad6d73a059eae2f4e6c8c2e49f67e353a95cef7c55b646280efd219793acf5` |
| pair_forest_accounts.rs | `lane_sequences_at` (new) | - | - | 571-581 | `a5f772b3a4ed2620611ad67efd722428bf58d921b465021183a922696995dba2` |
| pair_terminal.rs | `decode_pool_v1_pair_verified_afterstate_v1` | 161-233 | `dee26b6956fd57e2621ebfa8058b33e5ce9d0e83ac693fd78016ee28e78aa19b` | 161-192 | `a10c0459c6bf447b233f556cb1834165a15cb50ce11c57fd1953871cff06573f` |
| pair_terminal.rs | `decode_afterstate_frontier_v1` (new) | - | - | 455-467 | `f96857b040feabe424ca36868d1d1f981708edab5cb3394e76b7b12e0ce98ec9` |
| pair_tree_profile.rs | `decode_pool_v1_pair_live_snapshot_v1` | 500-625 | `c1ef0e8b66fa30cb45988eb8202695e368c206d00e582d661ff32910077c081d` | 500-544 | `59b6e2f17eafd5dd9733ead2991a87ea18f4ad866448ef01f402140fa92e6671` |
| pair_tree_profile.rs | `decode_live_snapshot_frontier_v1` (new) | - | - | 693-707 | `cbb156dd16cf04c2b65158d1d40b4f9da7ba0cf26739806c173d6c09a1128771` |

Every later non-test function in the same three files keeps its body and moves by the size difference: in
`pair_forest_accounts.rs` by -4 after `validate_master`, by -8 after the master decoder and by -12 after the
checkpoint decoder (for example `encode_pool_v1_pair_forest_master_v1` 233-259 becomes 229-255, same hash
`e17ec868c8545688294688e4c7560ae04ac06bd039d0c2a2f11045a8cec37621`); in `pair_terminal.rs` by -41 (for example
`exact` 235-239 becomes 194-198); in `pair_tree_profile.rs` by -81 (for example
`encode_pool_v1_pair_late_public_statement_v1` 627-659 becomes 546-578). The new helpers sit directly before
each file's test module, which keeps the shift as small as the shorter bodies allow.

tp3-core1 changes no Pool-linked function: the Pool ELF is byte-identical.

## 7. Release-style emission of the rewritten scope

Tree `src-tp3-all` = `src-base2` + tp3-dec2 + tp3-core1. Second pair, deployed features, overflow checks on,
Aeneas WITH `-abort-on-error`, each crate as the local crate in its own run.

| Run | Charon | Aeneas (abort-on-error) | Lean (4.32.0, L187 objects, probe adaptations) | Completeness vs Charon | Erased-region mutable type arguments |
|---|---|---|---|---|---|
| aspis-statement, `T3-C12`/`T3-A12`/`T3-L12` | exit 0, 1:50, 1.37 GB; LLBC `fcb98ef9a9877f8262f09b60cf432b8a15f7b7079a3624dd0cd6961ad5fded92` | exit 0, 31 s, 0.32 GB; Funs.lean `753062984aca66a33fe527bc04400f65d7856ff7d1269b6c278e056ac443a8c9` | Types, FunsExternal, Funs: all exit 0; no `sorry` | 187 local functions with a body; all emitted except 27 derived `Clone::clone` of Copy types (listed by the scan; no emitted body calls them) | none |
| aspis-core, `T3-C14`/`T3-A14`/`T3-L14` | exit 0, 23 s, 0.75 GB; LLBC sha256 `cb6f38ff41cb1916fccfb490a759c32d3eaeacc9cfdef6b6fc7cc3235e49e197` | exit 0, 27 s, 0.27 GB; Funs.lean `84655194872dc91e3b5f64987e37a12be10f60ec1755dc18dbe46e5b02f092f4` | Types, TypesExternal, FunsExternal exit 0; Funs exit 1, one error: `r0::heap::filled`, unknown identifier `alloc.alloc.Global` | 136 local functions with a body; all emitted except the derived `Clone::clone` of 8 Copy types and the derived `PartialEq::eq` of `M31` and `CM31` | none |
| aspis-core inverse pair, first pair, `T3-C10`/`T3-A10`/`T3-L10` | exit 0 | exit 0 (run without abort-on-error) | exit 0 | `CM31::inv`, `CM31::inv_with` emitted | not run |

Choices in the core run, stated so they are not found later: `crate::field::_::inv` is opaque and
`crate::field::_::inv_with` is excluded. The impl-qualified pattern `{aspis_core::field::CM31}::inv` did not match
in Charon, so the wildcard makes `M31::inv` and `QM31::inv` opaque too; both are emitted, and elaborate, in the
non-aborting run `T3-A09`/`T3-L09` of the same source. `r0::heap::uninit` is opaque.

Axioms in the external files, by kind. Statement: the four payment codec functions (another worker's
boundary), the aspis-core items the decoders call (`M31::{ZERO, from_le_bytes, to_le_bytes, clone, eq}`, linked
by the core emission), and std `PartialEq` for arrays and `Option`. Core: std `Array::map`, array `IntoIter`,
`Option` `?`, `Vec::try_reserve_exact`, and the opaque `inv` functions and `uninit`.

What elaborates, in one line per crate:
- Statement decoders on the path: all of them. Linked-only: all of them.
- Core on the path: everything except `heap::filled` (library gap), `heap::uninit` (not translated, unsafe) and
  `CM31::inv` / `CM31::inv_with` (settled first-pair gates; the first-pair emission elaborates).

## 8. Files

In `docs/research/future-version/translatability/core/`:
- `tp3-dec2.patch`, sha256 `2285fd6b03e5443ae06e171603bd6622986cb13bc1fe1a3287ebb41f595ff444`
  (aspis-statement only);
- `tp3-core1.patch`, sha256 `bb4d54aa559e9decc4a37979648b40e5a0324bc3b33e71fa1987c0f5f2bf8f2c` (aspis-core only);
- `tp3-fmt-test.patch`, sha256 `72178230466b3009f56e377a9c68729f81e44aecb863f8cd66113f8c8e61ab27`
  (one test line, section 9);
- `tp3_fnranges.py`, sha256 `35c26431711925d364a9a15fb037e35455858e58c3054c24f4e22a270d9a3361` (line ranges and body hashes);
- `tp3_erased_scan.py`, sha256 `ba40e0671ba039b46d6b1ff751c24b31841dd04c4f832f6921415cebc6a3f45d`
  (LLBC scan and span-based completeness check).

Host scripts in `evidence/future-version-20261111/host/`: `fv_tp3_lean.sh`, `fv_tp3_pool.sh`, `fv_tp3_tests.sh`.
On the host: specs, LLBCs, emissions and Lean sources under `tp3-xp/` and `lean-src/AspisTP3*`; trees
`src-tp3-base`, `src-tp3-dec1`, `src-tp3-dec2`, `src-tp3-core1`, `src-tp3-fmt`, `src-tp3-all`.

## 9. The failing statement test at the head

`pool_v1::format::tests::format_binding_pins_existing_primitives` fails at the unchanged head and at the pin.
It asserts `POOL_V1_FORMAT_BINDING[8..21] == [2,2,1,3,1,20,8,1,1,1,1,1,1]`; the value is
`[2,2,1,3,1,20,8,1,1,2,2,1,1]`. Bytes 17 and 18 are `POOL_V1_VERIFIER_REGISTRY_VERSION` and
`POOL_V1_VERIFIER_ENTRY_VERSION`, which commit `9c79ce5f9f8` (2026-10-15, "Persist canonical registry and
ProgramData bumps in revised account formats", design note `J1-G8-REGISTRY-BUMPS-20261015.txt`) raised from 1 to
2 on purpose: old revisions are rejected and no migration is provided. The test was not updated. `tp3-fmt-test.patch` updates
the one expected line; with it the format tests pass (`T3-TF2-fmt`: 3 passed). The README table of `pool_v1`
still lists ASRG and ASRE as v1, which is documentation drift and was not changed.

## 10. What remains

- `r0::heap::uninit` (on the path through the verifier's `claims`): named gap. Tool message "Raw ptr casts are
  only supported between pointers to literal types". The only safe stable form aborts on allocation failure
  instead of returning `Error::Allocation`, so it was not adopted. Needs an opaque specification or a translator
  change.
- `r0::heap::filled`: translated. Its Lean fails on the library's name for the global allocator, so it needs a
  library row; no source change can fix it.
- The four fast kernels: they translate and elaborate. Their equality with the plain kernels is owed (tested,
  not proved).
- The Aeneas `simplify_trait_calls` drop, and the derived Clone/eq omissions: on the translator lane's list.
  Every release emission must use the completeness check.
- `encode_pool_v1_pair_forest_terminal_statement_v1` ("Could not match the contexts"): not linked in the
  one-transaction verifier. It is linked in the Pool if the Pool calls it, and it is not in this pass's scope.
