# Aspis one-transaction verifier: extraction probe

Status: target not yet established. This note records which of the changed and
new verifier functions the Charon and Aeneas tools translate to Lean, which
they do not and why, and the smallest source change that would make each
failing function translate. It is a tool probe. It proves nothing about the
functions, and a translated function is not a verified function.

Source probed: branch `future-version`, commit
`6449f9b52078c72c9563f2912950f1bfa5d91cfb`. The existing verifier ("R1") is the
PIN2 source `c7593d23fdc56fcee9a9df1628d5f63b52ac7a95`. The crate and program
sources differ from that pin in 14 files (`git diff --stat c7593d23fdc..HEAD`),
`Cargo.lock` is unchanged, and three `Cargo.toml` files gained feature lines
only.

Sections 1 to 3 were written from reading only, before any tool was run, so
that the run in sections 4 onward can be judged against them. A prediction is
not a result.

## 1. Recipe as found (read, not run)

### 1.1 Tools

Two tool pairs exist on the build host. Both were used for R1.

| Pair | Charon | Aeneas | Rust toolchain | Used for |
|---|---|---|---|---|
| second pair | 454586e9, sha256 `57aa2359…f851`, driver `6a6552bc…7845` | 0d21a9ec (main of 2026-11-09), sha256 `230ee9f0…df91` | nightly-2026-09-17 | all PIN2 re-extractions of the verifier crate |
| first pair | daad69be (0.1.223), sha256 `daad69be…6af8`, driver `efdbe5b8…8c45` | b59d5188-lean432-extended (a patched build), sha256 `c0cf4fcc…b958` | nightly-2026-06-01 in the October runs; nightly-2026-09-17 in the PIN2 run of `verify_observed` | the frozen `verify_observed` text; the PIN2 prover extraction; needed where the second pair stops on function-pointer types |

Paths: second pair at
`/home/dombarker/project-offloads/codex-pc-prov-p4x-20261110/PCWH_T004_out/bin/{charon,aeneas}`;
first pair at
`/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/{charon,aeneas-b59d5188-extended}`.
A third Aeneas, 959659a6 (unpatched), was used with Charon daad69be for the
PIN2 adapter route (`evidence/prov-p9a-20261110/PIN2_ADAPTER_REPORT.json`).
The privacy stream's translator `aeneas-pvfix3` is a further patched build of
the first pair's Aeneas; it is not used here.

Sources read: `PW8_TOOLS.json`, `PW8_mkspec.py`, `PW8_extract.py`,
`PW8_run.py`, `PW8_run_host.py`, `PW8_stage.py`, `PW8_E002_spec.json` on
branch `fix/pin2-lean-20261110` (commit c8b641cae0e) under
`docs/research/100bit-spend-path-20261013/evidence/pin2-w8-20261111/`;
`evidence/extraction-repro1-20261027/XRa_PIN.md`, `XRa_HANDOFF.md` and the
command files there;
`docs/research/100bit-spend-path-20261013/lean-candidates/s4-minimal-fixed-calls-v10-20261021/extraction/`
(README, config, `run-stage.py`); the soundness lead's recipe forwarded by the
coordinator.

### 1.2 Commands

Charon, verifier crate scope (from `PW8_E002_spec.json`, the options common to
the PIN2 runs):

```
charon cargo --preset aeneas --mir built --sysroot default
  --include core::option::Option --include core::result::Result
  --include core::option::_::ok_or
  --start-from <root> ...        (one per root)
  --opaque <path> ...            (one per boundary)
  --include <type or item> ...   (types the roots mention)
  --dest-file <out>.llbc
  -- --manifest-path <workspace>/crates/aspis-r1-cost-probe/Cargo.toml
     --locked --offline --release --lib --jobs 4 --features <list>
```

Environment: `RUSTUP_TOOLCHAIN=nightly-2026-09-17`, `CARGO_NET_OFFLINE=true`,
`CARGO_BUILD_JOBS=4`, `RAYON_NUM_THREADS=1`,
`RUSTFLAGS="-Zthreads=1 -C link-arg=-Wl,--threads=1 -C overflow-checks=yes"`,
`CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true`,
`CARGO_PROFILE_RELEASE_CODEGEN_UNITS=2`, own `CARGO_TARGET_DIR`. The October
recipe (`run-stage.py`) also included `core::result::_::map_err` and used
`--no-default-features` and `--jobs 1`.

Aeneas:

```
aeneas -diagnose-translation -sequential -no-progress-bar -abort-on-error
  -backend lean -namespace <NS> -dest <dir> -subdir <NS> -split-files <in>.llbc
```

R1 features: `private-leaf-salts,optimized-terminal,program-build` for the
verifier crate; `pool-adapter,private-leaf-salts` for the program crate, with
`stage1`, `stage2`, `lifecycle_*`, `close_checkpoint` and
`solana_account_info::AccountInfo` opaque, and overflow checks off for the
program crate (release default; the emission is tagged as such in the adapter
report). R1's caps: MemoryHigh 3G, MemoryMax 4G, no swap, TasksMax 64, timeout
180 s, one at a time. Recorded sizes: Charon 34 to 86 s and 0.55 to 0.58 GB;
Aeneas 4 s and 0.29 GB for one function.

Overflow checks matter to the result. With them on (verifier crate recipe), `+`,
`*` and `>>` are translated as checked operations that fail on overflow. With
them off (the privacy stream's prover run, and R1's program crate run), Charon
emits wrapping operations.

### 1.3 Departures this probe makes from the W8 scripts

The W8 controller cannot be copied verbatim: it stages a payload pinned to
c7593d23fdc, reads specs from `research`, and launches its own systemd scope
with a 3G/4G assertion, while this probe must run every job through
`fv_slot.sh` (6G high, 8G max, no swap, TasksMax 256). The probe therefore
keeps the Charon and Aeneas command lines and environment above unchanged and
replaces only the launcher, the payload (a `git archive` of 6449f9b5207) and
the paths. Identity of the emission with a W8-style run is therefore by
command line, not by controller hash.

### 1.4 Where R1's emissions are

L187 closure: `/home/dombarker/project-offloads/codex-cx-replay-l187-20261109/{objs,src}`
(read-only local source copy used for lookups). PIN2 emissions:
`PIN2_NEWGATE_r0`, `PIN2_NEWGATE_r1_semantic`, `PIN2_NEWGATE_verifyprefix`,
`PIN2_NEWGATE_adapter_route_{Funs,Types}` in
`/home/dombarker/project-offloads/pin2-overlay-20261111/overlay-PIN2`.
Verdict vocabulary of the soundness lead (`PW8_compare.py`): identical,
tool-option adaptation, changed-new-gate, cannot-extract.

## 2. Known failure classes (read from the evidence)

From R1's table of functions no tool has extracted
(`evidence/prov-p6k-20261110/PCXN_CANNOT_EXTRACT.json`, 21 entries; claim draft
4.9a and 14k to 14s), from the privacy stream's prover table
(`evidence/pv-extract-pin2-20261111/data/CANNOT_EXTRACT.json` on
`codex/pv-extract-pin2-20261111`, 111 rows), and from the loop pass of the
second pair's Aeneas source (`src/PrePasses.ml`, lines 392 to 654 of the
source archive beside the binary), which states the loop rules exactly.

| Class, in plain words | Construct | Tool and message |
|---|---|---|
| return in a nested loop | `return` or `?` inside a loop that is inside another loop | Aeneas, both pairs: "Returns inside of nested loops are not supported yet" (R1: `prepared_claim`, `require_distinct_accounts`) |
| return in a loop with a branching tail | `return` or `?` inside a `for` or `while` whose following statements, in the same block, do not run straight to the function's return (any `if`, `match` or `?` after the loop) | Aeneas second pair: "Early returns inside of loops are not supported yet" (PrePasses.ml:576; R1: `decode_lane_from_pool_release`). First pair: uncaught `Not_found` at InterpReduceCollapse.ml:1991 |
| break to an outer loop | labelled `break`, or control flow that needs one | "Breaks to outer loops are not supported yet" (R1: `verify_in_place`) |
| function-pointer type | `Observer = Option<fn(Phase)>` in a signature; a function item passed as a value | Aeneas second pair: "Arrow types are not supported yet" (R1: `mark`, `tx2_common`, `query_loop`, `finish_relation`). The first pair's patched Aeneas accepts them |
| slice iterator | `.iter()`, `for x in &array`, `.windows()`, `.chunks_exact()`, `.enumerate()`, `.rev()`, `.fold()`, `.copied()`, `.any()`, `.all()`, `.zip()` | First pair: Charon type error on the core slice iterator impls. Second pair: Charon passes; Aeneas either crashes (`.copied()`: sanity check at SymbolicToPureTypes.ml:1005), or emits Lean that refers to models the Lean library lacks (Windows, fold, rev), or fails in the join below |
| loop borrow join | an iterator or reference whose borrowed content changes from one loop iteration to the next | "Joining region abstractions containing shared loans whose shared value contains borrows is not supported yet" (R1: `decode_k`, `claims`); "Could not join the contexts"; "Could not match the contexts" |
| mutable iterator | `iter_mut()`, `for x in &mut v`, `chunks_exact_mut` | emitted Lean instance does not typecheck (prover: `IterMut`, `ChunksExactMut`) |
| closure instance | capturing closures used through `FnMut`/`FnOnce` (for example by `core::array::from_fn`) | emitted Lean instance does not typecheck (prover, 5 rows) |
| nested borrow | `&mut &mut T`, a closure capturing a borrow of a borrow | "Nested borrows are not supported yet" |
| raw pointer or unsafe | `&raw mut`, pointer casts, foreign calls | "Unsupported operation" |
| shift amount type | with overflow checks off, `x >> 31` becomes `wrapping_shr` with an `i32` amount | Lean type mismatch (prover, 42 rows; fixed on the translator side there). Not expected with checks on |
| account wrapper | `AccountInfo` field access; drop of a `RefMut` guard | R1: `stage1`, `stage2` (InterpBorrows.ml:2731; "Can't retrieve the variants of non-adt type") |
| Lean library or naming | a constructor used as a function while its type has the same name (`M31`); constants built by array repeat; missing library constants | Lean elaboration errors (prover) |
| host-only branch | code under `#[cfg(target_os = "solana")]` | not an error: the tools run on the host target and translate the other branch |

Two further points read from the code, both bearing on the predictions:

- `if cfg!(feature = "…")` is an ordinary `if true`/`if false` in the code
  Charon reads (`--mir built` is before constant branches are removed), so the
  branch that is off in the deployed build may still be translated and its
  callees pulled in. `#[cfg(feature = "…")]` blocks do not have this effect.
- R1's own code shows the shape the tools accept: each fallible loop sits in
  its own small function whose loop is followed only by the final value
  (`push_byte_products`, `partial_dot`, `high_dot`, `shared_partials`,
  `finish_query_dot` in `weights.rs` and `verifier.rs`), array reads go through
  one-line helpers (`index_at`, `value_at`, `batch_key_at`), and `while` index
  loops replace iterator loops (`batch_tree`). Several new Aspis functions do
  not follow that shape.

## 3. Predictions, per target function (made before any run)

"Second pair" and "first pair" as in 1.1. Confidence is my own estimate.

### 3.1 Field kernels, `crates/aspis-core/src/field.rs`

| Function (feature) | Constructs seen | Prediction |
|---|---|---|
| `QM31::mul`, sixteen-product form (future-fast-kmul) | straight-line `u64` arithmetic; local `const PP`; closure `partial` capturing the local `p`; `x >> 31` with an `i32` literal; `wrapping_add`, `wrapping_sub` | Translates under both pairs and the Lean elaborates (80%). Risk: the capturing closure (R1's `canonical::Q::raw` has the same closure but it captures nothing) |
| `PreparedQm31Multiplier::mul` (future-fast-prepared) | rebuilds the operand and calls `QM31::mul` | Translates and elaborates (90%, given `mul`) |
| `QM31::square` (future-fast-square) | as `mul` | Translates and elaborates (80%) |
| `QM31::mul_add` (future-lazy-horner) | as `mul` | Translates and elaborates (80%) |

### 3.2 Semantic layer and wire

| Function (feature) | Constructs seen | Prediction |
|---|---|---|
| `semantic_boundary` (future-lazy-boundary), r1_semantic.rs:82 | `for c in polynomial` over `&[QM31; 28]` (slice iterator); `sums.map(M31::reduce_u64)` (function item passed to array `map`) | First pair: fails in Charon (slice iterator). Second pair: Aeneas emits (60%); elaboration depends on Lean models for iterating `&[T; N]` and for `map` with a function item (50%). R1's form (`iter().copied().fold(.., QM31::add)`) is in R1's cannot-extract table, so the Aspis form may be an improvement |
| `semantic_value` with `mul_add`, r1_semantic.rs:140 | `.iter().rev().fold(QM31::ZERO, closure)`; closure captures `alpha`, `round` | Same as R1's `semantic_value`: second pair emits, Lean does not elaborate for want of `rev`/`fold` models (75%). First pair: fails |
| `ValidatedRecord::decode_k` (future-validated-decode), r1_wire.rs:212 | `for (value, part) in bytes.chunks_exact(32).enumerate()`; closure `limb` capturing `part`; no `?` inside the loop any more | Fails as R1's does: Aeneas loop borrow join on the `chunks_exact().enumerate()` iterator (70%); first pair fails in Charon |
| `Digest32::digest_into` (default method), aspis-core digest.rs:13 | `*out = self.digest(parts)` | Translates and elaborates (85%) |
| `SolanaDigest::digest_into`, programs/r1-cost-probe/src/lib.rs:20 | deployed branch: `unsafe` call of `sol_sha256` with pointer casts under `cfg(target_os = "solana")`; host branch: `*out = hashv(parts).to_bytes()` | The tools see only the host branch, which translates with `hashv` external (80%). The deployed branch is never translated: a finding, not a pass |

### 3.3 `fused.rs`

| Function | Constructs seen | Prediction |
|---|---|---|
| `parse_shape_summed` | slice-to-array comparison; `proof[9..16].iter().any(closure)` | Translates under the second pair with standard-library externals (70%); same shape as R1's `parse_shape`. Elaboration depends on library models for `any` and slice-array equality |
| `merged_keys` | `for` over a range; insertion sort with `while j > 0 && …`; `keys.swap` | Translates and elaborates under both pairs (75%); R1's `sort_batch_keys` is the precedent |
| `merged_tree` | `for key in keys` over `&[u64; 22]` (slice iterator); `return Err` and `continue` inside that single loop, straight-line tail; array equality `val[d-1] != leaf` | First pair: fails in Charon (slice iterator). Second pair: Aeneas translates (55%); risk is the iterator loop. R1's `batch_tree` avoided all three constructs (index `while` loop, helper reads) |
| `merged_merkle` | four calls | Translates if `merged_tree`'s signature does (85%) |
| `coefficients` | `for` over a range; `Vec` index writes; `filled(..).map_err(closure)?` before the loop; `if cfg!(…)` | Translates and elaborates under both pairs (75%) |
| `base_lanes_tight` (future-tight-base) | `&mut [u64]` to `&mut [u64; 416]` by `try_into`; `?` inside the outer `for`, followed by more loops and a `?`; three-deep index loops; `for limb in acc.iter_mut()`; closures `read`, `fold` | Fails (75%). Likeliest first error: the mutable iterator, or "Early returns inside of loops" for the `?` in the outer loop |
| `extension_lane` | closure `read` returning `Result`; `?` on `push` inside the inner `for k` loop (loop depth 2) | Fails under both pairs: return in a nested loop (95%) |
| `cubic` | straight-line | Translates and elaborates (90%) |
| `fold_sums` | `obs: Observer` parameter; `?` at loop depth 2 in two places; closure `push` taking `&mut EbyKDot`; `core::array::from_fn` with a capturing closure; `if cfg!(…)` keeping `base_lane` and `extension_lanes_tight` in scope | Fails under both pairs (97%): function-pointer type under the second pair, return in a nested loop under either |
| `summed_final_checks` | `obs: Observer`; `?` inside `for b in 0..6` followed by branching code; a second loop with `?` | Fails under both pairs (90%): function-pointer type under the second pair; return in a loop with a branching tail under either |
| `claims_bytes` | `out[..32].copy_from_slice(&x.to_le_bytes())` | Translates (85%); elaborates if the library models range indexing of an array and `copy_from_slice` |
| `equality_tables` | two-deep index loops, no return; `core::array::from_fn` with a closure capturing `r` | Aeneas translates (80%); the `from_fn` closure instance may not elaborate (50%) |
| `query_weight_mle_pairs` (future-d-pair-expansion) | closure `limbs`; `from_fn` with a capturing closure; `?` in the outer loop after the inner loop, straight-line tail | Aeneas translates under the second pair (65%); elaboration risk from `from_fn` and closures (50%) |
| `verify_summed_format` | `obs: Observer`; straight-line calls with `?`; `try_into().unwrap()` | Second pair: fails on the function-pointer type (90%). First pair with callees opaque: translates (70%) |

### 3.4 Other crate files

| Function | Constructs seen | Prediction |
|---|---|---|
| `multiproof::verify_counting_merged` | `let … else { return Counted::Short }` inside `while` inside `for` (depth 2); two `&mut` array references exchanged each level with `core::mem::swap(&mut cur, &mut nxt)`; `hash.digest_into(&[&tag, &cur[i], sibling], &mut nxt[w])`; `well_formed_merged` with `windows(2).all`, `iter().all` | Fails under both pairs (97%): return in a nested loop first; then the reference swap (nested borrow, and a loop state whose borrows alternate) |
| `multiproof::node_count_merged` | two-deep loops, no return inside; `copy_from_slice`; calls `well_formed_merged` | Second pair: Aeneas translates (70%); `well_formed_merged` needs `windows`/`all` models, as R1's `node_count` (emitted, not elaborated). Not called on the verifier's path |
| `Weights::mle_at` (future-d-inactive-tensor) | `return Err` at loop depth 2 and 3; `for (kind,k) in [(1,0),…]` over an array by value; `if cfg!(…)` keeping a closure with its own loop and return | Fails under both pairs (97%): return in a nested loop |
| `Transcript::resume` | constructor | Translates and elaborates (95%) |
| `candidate::merkle_verdict` | `match`; `nodes[used..].chunks_exact(8).any(closure with try_into().unwrap())` | First pair: fails in Charon (slice iterator). Second pair: translates with standard-library externals (60%); elaboration needs `chunks_exact` and `any` models, which the R1 library is not known to have |
| `fast_pairing::KbyKDot` (`new`, `push`, `finish`) | same shape as R1's `EbyKDot`; `if cfg!(feature = "future-lean-dot")` keeps `push_lean` and `push_limbs` in scope | Translates and elaborates under both pairs (85%) |

### 3.5 Adapter, `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs`

| Function | Constructs seen | Prediction |
|---|---|---|
| `stage2_owned`, one-transaction block (future-one-tx) | straight-line; `observer()` value of function-pointer type; function item `error` passed to `map_err`; `data.get(..4) != Some(&MAGIC[..])` | Second pair: fails on the function-pointer type (70%). First pair with R1's adapter options and the callees opaque: translates (60%) |
| `stage1` rejection (future-one-tx-lean), `stage2` buffer size, `scan_proof_buffer` length | `stage1` body is now a constant `Err`; `stage2` changes one constant; `scan_proof_buffer` changes one constant | `stage1` may now translate (its body no longer touches `AccountInfo`); `stage2` stays in R1's cannot-extract class (account wrapper); `scan_proof_buffer` as in R1 |

### 3.6 Predicted totals

Of the 27 rows above: 7 predicted to fail under both pairs
(`decode_k`, `base_lanes_tight`, `extension_lane`, `fold_sums`,
`summed_final_checks`, `verify_counting_merged`, `mle_at`); 2 more predicted to
fail under the second pair only (`verify_summed_format`, `stage2_owned`), where
the first pair is expected to work; 5 predicted to translate
only with standard-library items left external or with Lean that may not
elaborate (`semantic_boundary`, `semantic_value`, `parse_shape_summed`,
`merkle_verdict`, `node_count_merged`); the rest predicted to translate.

Predicted most expensive to repair: `verify_counting_merged` (three separate
obstacles in one loop nest), then `fold_sums`, `mle_at`, `summed_final_checks`.

Predictions end here. Everything below was written after the run.
