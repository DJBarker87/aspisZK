# Aspis one-transaction verifier: extraction probe

Status: target not yet established. This note records which of the changed and
new verifier functions the Charon and Aeneas tools translate to Lean, which
they do not and why, and the smallest source change that would make each
failing function translate. It is a tool probe. It proves nothing about the
functions, and a translated function is not a verified function.

Source probed: branch `future-version`. Sections 1 to 3 were written reading
commit `6449f9b52078c72c9563f2912950f1bfa5d91cfb`; every run used a payload
exported from `4045ecbdda3c4184a283ecfbf5df65805cd4114e`, which differs from it
in the crates and programs by eleven lines of `verify_summed_format` (the Merkle
authentication moved after the final sumcheck; no new construct). The devnet
source 8a4059c8bc2 was not probed. The existing verifier ("R1") is the
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

## 4. What was run

All jobs ran on the build host through `fv_slot.sh` (6G high, 8G max, no swap),
one at a time, 67 receipts named `XP-*` under
`~/project-offloads/future-version-20261111/receipts/`. No job was killed for
memory, none swapped, none timed out. Per-run figures are in
`extraction-probe/data/receipts.json`.

Tool hashes were checked against `PW8_TOOLS.json` before the first run and all
six match (Charon and driver of both pairs, both Aeneas binaries). Versions as
printed: Charon 0.1.315 and Aeneas 0d21a9ec (second pair, toolchain
nightly-2026-09-17); Charon 0.1.223 and Aeneas b59d5188-lean432-extended (first
pair, toolchain nightly-2026-06-01, which that Charon selects itself).

Feature sets used, exactly:

- verifier crate (`crates/aspis-r1-cost-probe`), all `XP-C01` to `XP-C15` except
  the program runs: `private-leaf-salts,optimized-terminal,program-build,future-validated-decode,future-merkle-single-pass,future-merkle-in-place,future-tight-base,future-tight-weights,future-lazy-boundary,future-d-inactive-tensor,future-d-pair-expansion,future-fold-shared,aspis-core/future-fast-kmul,aspis-core/future-fast-prepared,aspis-core/future-fast-square,aspis-core/future-lazy-horner`,
  overflow checks on;
- program crate (`programs/r1-cost-probe`), `XP-C07` to `XP-C09`:
  `pool-adapter,future-one-tx-lean,private-leaf-salts,future-fast-kmul,future-fast-prepared,future-fast-square,future-validated-decode,future-merkle-single-pass,future-merkle-in-place,future-tight-base,future-tight-weights,future-lazy-boundary,future-d-inactive-tensor,future-d-pair-expansion,future-lazy-horner,future-fold-shared`,
  overflow checks off, as in R1's adapter run;
- Pool crate (`programs/aspis-pool`), `XP-P01`, `XP-P03`, `XP-P04` (the spec
  `XP-P02` was written and not run):
  `r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit`
  (the set named for R1's Pool build in `R20-POOL-HANDOFF-AUDIT-20261020.md`;
  not confirmed here against the deployed build), checks off in P01, on in P03
  and P04.

Method. One Charon run per scope with the entry and the targets as roots and
R1's unchanged callees opaque (`prepare`, `QueryGeometry::for_range`,
`finish_relation_round`, `Weights::new`, the `WideExact` methods,
`heap::filled`, the leaf hash, the samplers, `trace`). Then Aeneas WITHOUT
`-abort-on-error`, so that one pass lists every function it rejects; R1's
emissions used that flag, and a release emission must too. The emitted Lean was
compiled one file at a time with `fv_lean.sh` against the R1 (L187) objects.

Two adaptations were needed to compile second-pair emissions against the R1
library, both of the kind the soundness lead calls tool-option adaptation:
headers (the emission uses Lean's module syntax and one linter option that Lean
4.32.0 does not know), and five library definitions the R1 library lacks under
the emitted names (`branch`, `from_residual`, `map_err`, `ok_or`,
`array::from_fn`), supplied by a small copied shim
(`extraction-probe/lean/AspisXPNewLib.lean`; two departures from the copied text
are stated in its header). "Elaborates" below means against the R1 library with
those two adaptations and with the emission's own `*_Template` axiom files
standing for opaque and external items. First-pair emissions needed neither.

Two things outside the brief's letter, stated so they are not found later: the
cargo runs used the host's ordinary cargo home for the offline registry, as the
W8 runs and this stream's own builds do; and one archive of the summaries was
written to the host's `/tmp` for a moment while copying them back and removed
in the same command. Nothing else was written outside `extract-probe`,
`lean-src`, `lean-out` and the wrapper's `receipts`.

Runs that failed through my own input, not through a tool limit: `XP-C07` and
`XP-C14` (a root pattern that matches nothing makes Charon exit 101 with no
message), `XP-L01`, `XP-L02`, `XP-L07` (header and shim errors), `XP-T02` (test
fixtures missing from the payload).

Cost. Charon: 31 to 112 s, of which the first run in each target directory is
the dependency build; peak process memory 0.60 to 0.69 GiB, scope peak 1.2 to
1.5 GiB. Aeneas on the verifier scope: 38 to 63 s and 0.33 to 0.45 GiB for
about 400 functions (one function, the unused `base_lane`, took 16.6 s; the
slowest target, `query_weight_mle_pairs`, 10 s). Aeneas on the Pool's terminal
handler: 57 s and 3.21 GiB, the largest figure of the probe and the only one
near R1's 4 GiB cap. Lean: 1 to 22 s per file, scope peak at most 0.46 GiB.
Nothing exceeded 4 GiB. A full extraction would be a handful of such scopes;
the Pool handler is the one to cap and watch.

## 5. Verifier list: what does not translate

Eight of the listed functions, and one helper they call, are rejected by the
translator as written. In every case a rewritten copy was then run and the
result is in the last column. The rewritten copy is
`extraction-probe/rewrites-tested.patch` (729 lines of diff over six files);
it exists only in the probe's work directory and was never applied to the
repository.

| Function | Tool message, source as written | Smallest rewrite that was tested | Result on the rewritten copy |
|---|---|---|---|
| `multiproof::verify_counting_merged` | Aeneas, second pair: "Returns inside of nested loops are not supported yet" (multiproof.rs 343-383) | one level per call in `merged_level` (a single loop that may return `None`); the eighteen levels run as nine pairs, `val` to `other` and back, so the two buffer references are never exchanged; a flag replaces the early return | translates and elaborates |
| `Weights::mle_at` | "Breaks to outer loops are not supported yet" (weights.rs 373-433) | every loop in its own small function, as R1's `high_dot` and `partial_dot` are; `mle_at` itself has no loop | translates and elaborates, after three rounds: with its last loop left inline Aeneas said "Unimplemented" and I did not find why |
| `fold_sums` | second pair: "Returns inside of nested loops are not supported yet" and "Arrow types are not supported yet"; first pair: "Could not read a borrow" at `let [f0, f1, f2, f3] = first` | each fallible loop in its own function; feature choices by `#[cfg]` instead of `if cfg!`; arrays of accumulators read by index through a by-reference `value()` | the helpers translate and elaborate under the second pair; `fold_sums`, which keeps the `Observer`, translates and elaborates under the first pair |
| `summed_final_checks` | second pair: "Returns inside of nested loops are not supported yet" and "Arrow types…"; first pair: "Internal error, please file an issue" (fused.rs 539-554) | the round loop in `final_rounds`, the final-message loop in `final_message_at` | as `fold_sums` |
| `extension_lane` | "Breaks to outer loops are not supported yet" (fused.rs 196-216) | the four pushes in a helper with one loop | translates and elaborates |
| `base_lanes_tight` | "Early returns inside of loops are not supported yet" (fused.rs 350-396) | per-query work and the periodic fold as loop-only helpers, the fallible loop alone, an index loop in place of `iter_mut` | Aeneas translates; the Lean does NOT elaborate. Still open: see below |
| `ValidatedRecord::decode_k` | "Joining region abstractions containing shared loans whose shared value contains borrows is not supported yet" (r1_wire.rs 235-241) | the loop in a function that receives only the byte slice | translates and elaborates |
| `verify_summed_format` | second pair: "Arrow types are not supported yet" (signature) | none: use the first pair for it, as R1 does for `verify_observed` | first pair, source as written: translates and elaborates |
| `relation_view` (helper, not on the list) | "There should be no bottoms in the value" (fused.rs 87-99) | the three empty slices from a named constant | translates and elaborates |

Why each one fails, in a sentence, since the reasons are what to keep in mind
when writing new code:

- A `return` or `?` may sit inside one loop only, and only if nothing but
  straight-line code follows that loop. Two loops with `?` in one function fail
  even when they are not nested, because the translator moves what follows the
  first loop into it. Hence one fallible loop per function.
- `&self` on a type that holds a reference, plus a loop in the same function,
  fails (`decode_k`, and R1's own `decode_k` for the same reason). Changing the
  loop form or removing the closure did not help; moving the loop out did.
- `let [a, b, c, d] = array` on an array of values that are not `Copy` fails
  under both pairs.
- A literal `&[]` returned inside a struct fails, because the translator reads
  the code before the compiler turns that literal into a constant.
- A function with an `Observer` parameter can only go through the first pair,
  and the first pair's Aeneas is the weaker of the two on loops, so such a
  function has to be a thin straight-line wrapper.
- `if cfg!(feature = …)` keeps the branch that is off in the model: `base_lane`,
  `extension_lanes_tight`, `query_weight_mle`, `push_lean` and
  `canonical_scan_words` were all translated although the deployed build never
  runs them, and two of them fail. `#[cfg]` blocks drop them (the LLBC shrank
  from 27.5 MB to 7.9 MB on the rewritten copy).

`base_lanes_tight` remains open. After the rewrite the translator accepts it,
but the emitted Lean needs two models the R1 library does not have: indexing a
`Vec` by a full range, and converting `&mut [u64]` to `&mut [u64; 416]`. Either
those two standard-library items get models (the R1 route for such items is a
library row, not a source change), or the accumulator becomes a
`Vec<[u64; 16]>` with one row borrowed per lane, which is R1's `BatchedWeights`
shape and is already proved to translate; that adds about one bounds check per
lane per query and must be measured.

The owner's three checks, for the rewrites as a set:

1. Compute units. Not measured. Every helper is `#[inline(always)]` and the
   arithmetic is unchanged, so no increase is expected from `mle_at`,
   `fold_sums`, `summed_final_checks`, `extension_lane`, `relation_view` or
   `semantic_value`. Three places could move the count and need a measurement
   before adoption: `verify_counting_merged` (a flag test per level pair and an
   `Option` return per level, against a reference swap that was free),
   `decode_k` (a slice range check per value where `chunks_exact` gave none),
   and `well_formed_merged` (no early exit on a malformed index set).
2. Same value. Tested, not proved: the rewritten copy passes the thirteen
   existing tests that compare these kernels with their references and replay
   the six saved proofs with every-region mutations (`XP-T03`: 13 passed, 0
   failed, release build). That is one test run on fixtures. A differential
   test of old against new on random inputs, in particular for
   `verify_counting_merged` and `well_formed_merged`, is still owed.
3. Prover and published material. The patch touches only
   `crates/aspis-r1-cost-probe/src/{fused,weights,multiproof,r1_wire,r1_semantic,fast_pairing}.rs`.
   It changes no proof byte, no transcript row and no constant. It adds three
   by-reference `value()` methods beside R1's `finish` in `fast_pairing.rs`
   and leaves `finish` as it is. `weights.rs`, `r1_wire.rs` and
   `fast_pairing.rs` are also compiled into the prover, so a change there
   moves the prover's build even though no prover function changes; that needs
   the owner's leave.

## 6. Verifier list: per-function table

Second pair unless stated. "R1 has" answers whether R1 already holds an
extraction of an unchanged version: for every row the answer is no, because
each function is either new or changed under the Aspis features; the column
says what R1 holds of the earlier form. Full records, with the prediction
outcome per row, are in `extraction-probe/data/verdicts.json`.

| Function | Translated | Emitted Lean | R1 has | Verdict |
|---|---|---|---|---|
| `QM31::mul`, sixteen-product form | yes | elaborates, no axiom | earlier form, several modules | changed-new-gate |
| `PreparedQm31Multiplier::mul` | NOT ESTABLISHED: present in Charon's output, but Aeneas emitted no definition and no error for it (`CM31::mul` likewise), in two runs | none | earlier form (RPu_FIq_Native01) | open |
| `QM31::square` | yes | elaborates, no axiom | earlier form | changed-new-gate |
| `QM31::mul_add` | yes | elaborates, no axiom | none (new) | changed-new-gate |
| `semantic_boundary` | yes | elaborates; one standard-library axiom (array `map` with a function item) | none: R1's form is in R1's cannot-extract table | changed-new-gate, an improvement on R1 |
| `semantic_value` with `mul_add` | yes | usable only with reversed-iterator `fold` as an axiom and an iterator instance that does not elaborate | none (R1: emitted, never elaborated) | rewrite recommended (index loop: tested, no axiom) |
| `ValidatedRecord::decode_k` | no | placeholder | R1's form is cannot-extract | cannot-extract; rewrite tested |
| `Digest32::digest_into` (default) | yes | elaborates | none (new) | changed-new-gate |
| `SolanaDigest::digest_into` | host branch only (first pair) | elaborates | none (new) | see finding 1 |
| `parse_shape_summed` | yes | elaborates; axiom for `any` on a slice iterator | `parse_shape` (same shape) | changed-new-gate |
| `merged_keys` | yes | elaborates, no axiom | none | changed-new-gate |
| `merged_tree` | yes | elaborates; two axioms for `>>` and `&` applied to `&u64` | `batch_tree` (different shape) | changed-new-gate; `for &key in keys` removes both axioms (tested) |
| `merged_merkle` | yes | elaborates | none | changed-new-gate |
| `coefficients` | yes | elaborates | none | changed-new-gate |
| `base_lanes_tight` | no | none | none | cannot-extract; open after rewrite |
| `extension_lane` | no | none | none | cannot-extract; rewrite tested |
| `cubic` | yes | elaborates | none | changed-new-gate |
| `fold_sums` | no, either pair | none | none | cannot-extract; rewrite tested |
| `summed_final_checks` | no, either pair | none | none | cannot-extract; rewrite tested |
| `claims_bytes` | yes | elaborates | none | changed-new-gate |
| `equality_tables` | yes | elaborates | none | changed-new-gate |
| `query_weight_mle_pairs` | yes | elaborates | none | changed-new-gate |
| `verify_summed_format` | first pair only | first-pair emission elaborates unadapted | none | tool-option adaptation |
| `verify_counting_merged` | no | none | none | cannot-extract; rewrite tested |
| `node_count_merged` | yes | elaborates; its callee `well_formed_merged` needs `windows` and `all` as axioms and an instance that does not elaborate | `node_count` | changed-new-gate; index-loop `well_formed_merged` tested, no axiom |
| `Weights::mle_at` | no | none | none | cannot-extract; rewrite tested |
| `Transcript::resume` | yes | elaborates | none | changed-new-gate |
| `merkle_verdict` | yes | elaborates; axiom for `any` over `chunks_exact` | same expression inside R1's `batch_tree` | changed-new-gate |
| `KbyKDot` (`new`, `push`, `finish`) | yes | elaborates | `EbyKDot` (same shape) | changed-new-gate |
| `stage2_owned`, one-transaction block | first pair only | first-pair emission elaborates | the two-transaction body (AdapterRwModel) | tool-option adaptation |
| `stage1` rejection, `scan_proof_buffer` | yes (first pair) | elaborate | `stage1` was cannot-extract in R1 | changed-new-gate |

Against the predictions: of the seven functions predicted to fail under both
pairs, all seven failed, though two with a different message than predicted
(`extension_lane`, `mle_at`: "Breaks to outer loops" rather than "Returns
inside of nested loops"). The two predicted to need the first pair did. Wrong
or missed: `relation_view` was not predicted at all; `PreparedQm31Multiplier::mul`
was predicted to translate and is not established; `semantic_boundary` and
`merged_tree` did better than feared; and the first pair's Charon did not fail
on slice iterators as the October evidence led me to expect.

## 7. Findings beyond the table

1. The deployed SHA-256 call is invisible to the tools. On chain,
   `SolanaDigest::digest_into` is an `unsafe` call of `sol_sha256` with pointer
   casts, written in Aspis source (programs/r1-cost-probe/src/lib.rs 22-26).
   The tools run on the host target and translate the other branch,
   `*out = hashv(parts).to_bytes()`. The emitted Lean therefore describes code
   that is not deployed. R1's `digest` goes through the SDK's `hashv`, which a
   runtime trust row covers; this block is Aspis code, and the owner's rule is
   that Aspis code is not a trust row. Options: call `hashv` and assign (safe,
   translatable, costs the 32-byte copy that this function exists to avoid;
   must be measured), or keep the block and state for it an explicit
   specification the owner accepts. Not decided here.
2. `PreparedQm31Multiplier::mul` and `CM31::mul` are silently missing from
   every second-pair emission although Charon outputs them. No error, no
   placeholder. I did not find the cause. Until it is found, a release
   emission must be checked for completeness against Charon's declaration
   list, not only for errors.
3. Where translation succeeds only through something left opaque or external.
   (a) Standard-library items that become axioms in the emission and would
   each need a model or a library row: `Iterator::any` (in `merkle_verdict`,
   `parse_shape_summed`), `windows` and `all` (`well_formed_merged`),
   reversed `fold` (`semantic_value`), array `map` with a function item
   (`semantic_boundary`), operators on `&u64` (`merged_tree`). The rewritten
   copy removes all of them except the two `any` uses and the `map`.
   (b) Boundaries I chose, which R1 also keeps opaque and which carry R1's
   existing specifications or obligations: the `WideExact` methods,
   `heap::filled`, the leaf hash, the samplers, `prepare`, `for_range`,
   `finish_relation_round`, `Weights::new`. (c) Under the first pair,
   `verify_summed_format` and `stage2_owned` were translated with every callee
   external, so those emissions say nothing about the callees.
4. R1 functions on the path that a fresh emission does not handle:
   `factored_s2_libra_weights` translates but its Lean fails on a name clash
   (a local named `weights` inside module `weights`); R1 holds a gate version.
   `mark` and `prepare` have the function-pointer type and need the first
   pair, as in R1.
5. The first pair's Aeneas stops on an uncaught exception (`Not_found`,
   InterpReduceCollapse.ml:1991) when given the whole scope, without naming a
   function (`XP-A02`). It was therefore used only on narrow scopes.

## 8. Pool payout path (second list)

Added by the lead after an owner decision that the withdrawal payout is inside
the proved game. The Pool sources are those of the pin and the probe proposes
no change to them. Predictions were written before any Pool run and are kept
unchanged in `extraction-probe/POOL-PREDICTIONS-BEFORE-RUN.md` (sha256
`3564e8d2…5efb`). Second pair only; the first pair was not run on the Pool.
Runs `XP-P01`/`XP-PA01` (narrow scope, checks off), `XP-P03`/`XP-PA03` (same,
checks on), `XP-P04`/`XP-PA04` (terminal handler, checks on); Lean `XP-L16`,
`XP-L17`.

What does not translate:

| Function | Tool message | Would an opaque callee with a stated specification suffice? |
|---|---|---|
| `vault::exact_five_withdrawal_accounts` (vault.rs 352) | "Returns inside of nested loops are not supported yet" (the pairwise key comparison) | Yes. Its content is: exactly five accounts, pairwise distinct keys, returned in order. As an opaque function with that specification it unblocks its three callers' signatures. It is Aspis code, so by the owner's rule that specification is an open obligation, not a trust row |
| `vault::plan_legacy_withdrawal_transfer_from_identity_v1` (387) | "Unreachable", raised at the call of `require_token_owned_account` (vault.rs 198-207): passing `&AccountInfo` to another function | Not by one boundary. The body passes account references to helpers and borrows account data three times; each of those is the failing construct. The destination check at 454 and the amount arithmetic are plain code but sit inside this body |
| `vault::validate_exact_withdrawal_delta_v1` (551), the re-read of both balances | "Unreachable" at `AccountInfo::try_borrow_data` (solana-account-info lib.rs 121) | Yes in principle: `try_borrow_data` opaque with the specification "returns the account's current data" is an SDK item. The call still has to be accepted by the translator, which this run does not show |
| `vault::exact_withdrawal_transfer_account_infos_v1` (535) | "Unimplemented" (cloning five `AccountInfo`) | Yes: `AccountInfo::clone` is an SDK item |
| `pair_forest::process_pair_forest_terminal_with_verifier_v1` (1615-1821), which holds the withdrawal branch (plan at 1695-1707, execution at 1785-1793) | "Unimplemented: found an occurrence of a lifetime constraint relating…" on the signature and the body | No. The signature itself (two closure parameters, one of eleven arguments, tied to the accounts' lifetime) is rejected, so no choice of opaque callee helps. The token transfer already goes through a trait method (`PoolCpiRuntimeV1::invoke_signed`), which is the right place for a specification of the transfer, but the function around it does not translate |
| `pair_forest_dispatch::plan_pair_forest_terminal_dispatch_v1` (144), the request re-encoding | "Unimplemented" | Not determined |
| `pair_forest_dispatch::plan_pair_forest_terminal_dispatch_with_bytes_v1` (177) | "Early returns inside of loops are not supported yet" | No: the loop is in its own body |
| `pair_forest_dispatch::invoke_pair_forest_terminal_with_runtime_v1` (281-383), the verifier call and return-data read | "Inconsistent projection" at 312 (`let [registry, entry] = registry_accounts else`) | No: the slice pattern on accounts is in its own body. The return-data handling after the call (354-383) is straight-line and is not what fails |
| callees of the handler outside the list | `require_unique_accounts` (nested returns), `decode_lane_account_from_program_invariant_v1` and `history::validate_root_page_bytes` (early returns in loops), `plan_pair_forest_nullifier_marker_consumption_v1`, `classify_nullifier_marker_account_v1`, `create_or_allocate_with_seed_with_rent` ("Unreachable" at account calls), `encode_lane_from_authenticated_result_v1` ("Could not match the contexts"), `registry::authenticate_verifier_selection_v1/_v2` ("Inconsistent projection" at a slice pattern), `require_checkpoint_distinct` ("Unreachable") | — |

What translates, and whether the Lean elaborates (checks on):

| Function | Translated | Emitted Lean |
|---|---|---|
| `vault::parse_legacy_mint_v1`, `parse_legacy_token_account_v1`, `parse_coption_pubkey`, `parse_coption_u64`, `token_array`, `require_zero` | yes | elaborate (SDK and standard-library items external: `Pubkey::new_from_array`, `any`) |
| `vault::require_token_owned_account` | yes | elaborates |
| `vault::pool_v1_vault_authority_address`, `pool_v1_vault_token_account_address`, `registry::stored_bump_address_matches` | yes | elaborate (`find_program_address`, `create_program_address`, `is_ok_and` external) |
| `pair_forest::validate_pair_forest_request_accounts_v1` (1321-1382), the request identity check | yes | elaborates with checks on. With checks off it does not: `1u8 << output_lane` becomes a wrapping shift whose amount type the library rejects |
| `pair_forest::lane_address_matches`, `pair_forest_dispatch::supported_loader`, `require_verifier_program` | yes | elaborate |

Three points for whoever plans the Pool's proof:

- `AccountInfo` itself is not the obstacle with the second pair: Charon emits
  it as an ordinary structure and functions that only read its plain fields
  translate and elaborate. What fails is handing an `&AccountInfo` to another
  function, borrowing account data, cloning, and slice patterns over accounts.
- One Aspis function used by every error path does not elaborate:
  `impl From<PoolV1ProgramError> for ProgramError` (an enum cast to `u32`).
  It affects which error code is returned, not acceptance, but every function
  that converts an error depends on it.
- The predictions were too pessimistic about the leaf checks (the request
  identity check and `require_token_owned_account` translate) and right about
  everything that composes them.

The payout path as a whole therefore does not translate as written, and no
single opaque callee makes it translate: the plan function, the handler and
the dispatch function each fail in their own bodies. What the probe can say
is which parts are plain logic that translates today (the token and mint
parsers, the address checks, the request identity check) and which parts are
account plumbing around them.

## 9. Not attempted, and why

- No first-pair run on the Pool, and no first-pair verdict for most verifier
  rows: its Aeneas crashes on the whole scope, and narrowing it function by
  function was not worth the slots once the second pair gave verdicts.
- No rewrite was tried for `base_lanes_tight` beyond the one reported, none
  for `merkle_verdict` or `parse_shape_summed` (they translate; the open point
  is the `any` axiom), and none for any Pool function.
- No compute-unit measurement of any rewrite, and no SBF build.
- No proof about any emitted definition. No equality with any R1 gate module
  was attempted; "changed-new-gate" here means only that a fresh emission
  exists and elaborates.
- The Aeneas test suite was not run, and the third Aeneas (959659a6, R1's
  adapter tool) and the privacy stream's patched translator were not used.
- `canonical_scan_words`, `validate_record_fields_lean`, the lean dot pushes
  and the other functions that section 10 of the soundness note marks as not
  in the deployed build were not probed, except where `if cfg!` pulled them in.

## 10. Where things are

In the worktree, uncommitted, for the lead to commit: this note;
`extraction-probe/data/` (verdicts, receipts, per-run error summaries, Lean
error maps, external-axiom lists, payload manifest);
`extraction-probe/specs/` (one JSON per Charon run); `extraction-probe/tools/`
(the scripts as run); `extraction-probe/lean/AspisXPNewLib.lean`;
`extraction-probe/rewrites-tested.patch`; the two frozen prediction files.

On the build host, not in the repository:
`~/project-offloads/future-version-20261111/extract-probe/` with `payload/`
(the archive, sha256 `c9fff866…999a`, 679 files, plus the twelve test
fixtures), `src/`, `src-rw/` (the rewritten copy), `runs/XP-*/` (each with
its command, log, `out.llbc` and `raw/` emitted Lean) and `target/`;
`lean-src/AspisXP*.lean` and `lean-out/AspisXP*.olean`.

Next deliverable: the owner's decision on finding 1 and on whether the
rewrites of section 5 are to be made before the freeze; then a compute-unit
measurement of the three rewrites named there, and a release-style emission
(with `-abort-on-error`, split by tool pair as in section 5) of the reshaped
source.

## 11. Addendum (lead, 2026-11-11): a translator defect that exits 0, checked against this probe

Reported by the soundness lead after the probe finished, found by the privacy stream and confirmed
on the verifier side (finding 27 on the research branch): the Aeneas lineage in use (959659a6 and
later, probably both tool pairs) silently drops a write made through a REVERSED mutable iterator
(`for x in s.iter_mut().rev() { *x = … }`). Charon emits the double-ended iterator over `IterMut`
with an erased region and the give-back is lost. The tool exits 0 and the emitted Lean is wrong.
Any function with that pattern cannot be extracted with the current tools, whatever the exit code.

Checked for Aspis, by search of the source at the branch head and of this probe's emissions (not by
the privacy stream's pre-pass, which has not been run here):

| Where | Pattern | Function | Status |
|---|---|---|---|
| `crates/aspis-r1-cost-probe/src/sampler.rs:61` | `quotient.iter_mut().rev()` | `low_base_p_digits` | Pinned R1 code, unchanged in Aspis, on the verifier's path. It is R1's known site; R1's closure does not use that emission (finding 27). Aspis reuses the sampler unchanged, so it inherits R1's treatment and needs nothing new, but the function stays in the cannot-extract class for Aspis too. |
| `sampler.rs:140`, `:155` | `rank.iter_mut().rev()` | `old_sample`, `old_pass` | Inside the test module; not compiled into the program. |
| `crates/aspis-core/src/r0_transcript.rs:129` | `rank.iter_mut().rev()` | `base_p_digits` | Pinned code. Confirmed by the soundness lead the same day: its audit covered this function, it has the same shape, it is not on the verifier's path, and it is not to be extracted with the current tools. |
| Functions changed for Aspis (`fused.rs`, `multiproof.rs`, `weights.rs`, `fast_pairing.rs`, `r1_wire.rs`, `r1_semantic.rs`, the field kernels, the adapter) and the rewrite patch | none | | No reversed mutable iteration anywhere. |
| Pool payout path | none | | No `iter_mut` at all in the emitted functions. |

Forward `iter_mut()` (not the reported defect) occurs in `base_lanes_tight` (`fused.rs:382`, the
function whose Lean does not elaborate, section 6), `accumulate_weights_tight` (`fused.rs:465`),
`Weights::materialize` (`weights.rs:353`) and `multiproof::verify_in_place` (`multiproof.rs:174`).

The probe's emissions, scanned for the symptoms the soundness lead named:
- No `Rev` over `IterMut` in any emitted file. The one `Rev` is over an immutable iterator
  (`semantic_value`'s reversed `fold`).
- `let _ ←` occurs three times in each verifier emission, in `coefficients_loop.body` (two
  discarded array reads) and `factored_s2_libra_weights_loop.body` (one discarded product). Each
  discards a value the Rust also discards. None is a value the Rust writes back.
- The forward `IterMut` loop of `base_lanes_tight` is emitted with its give-back function.

Consequences for the freeze:
- Nothing has to be reshaped in the changed functions because of this defect.
- A release emission must not rely on exit codes. In addition to the completeness check against
  Charon's declaration list (finding 2 of section 7), it must run the privacy stream's
  erased-region pre-pass (branch `codex/pv-itermut-20261111`, `src/MutInst.ml`) over every LLBC
  file, or scan the LLBC structurally for mutable-borrow type arguments with an erased region.
- The silent omission of `PreparedQm31Multiplier::mul` and `CM31::mul` (finding 2 of section 7) is
  now on the translator lane's list beside the write drop, and the soundness lead states the
  completeness check against Charon's declaration list as a hard requirement for any release
  emission on both streams.
- `base_lanes_tight` is the one changed function with a mutable iterator. Rewriting its loop over
  an index would remove the iterator and may also let its Lean elaborate. That is a source change
  with a compute cost to measure, so it is a proposal, not something done here.
