# Aspis frozen tree: one linked translation of the deployed verifier program (X1, stage 1)

Status: target not yet established. This is a tool record. It says which functions of the deployed program the
Charon and Aeneas tools translate in ONE run, and whether the emitted Lean elaborates against the R1 (L187) library.
Nothing in it is a proof. A translated, elaborated function is not a verified function.

## Result in short

- The single run worked; the fallback (five scopes joined by link modules) was not needed. One Charon run on the
  program crate, with the three library crates included, and one Aeneas run with `-abort-on-error` (exit 0), give
  one `Types` / `Funs` / `FunsExternal` set in one namespace, `AspisX1`.
- Primary emission `off2` (the deployed setting, overflow checks off): 714 rows. 684 translate and elaborate, 23
  translate and do not elaborate, 7 are named gaps (5 opaque by flag, 2 not in the emission). With overflow checks
  on (`on2`, not deployed): 703, 4 and 7.
- The bodiless declarations of the package (`externals.tsv`): 67. Functions: 39 std, 9 SDK, 5 Solana runtime, 5
  named gaps. Types: 7 std, 2 SDK. No other Aspis function is bodiless.
- Every one of the 27 Aspis declarations that the five-scope freeze emission left without a body now has a
  translated body, except `M31::inv` and `CM31::inv` (opaque in this run) and `CM31::inv_with` (not reached). Of
  those 27, `QM31::inv` and `heap::uninit` are not reached from the program entry at all.

## Tree and build settings

- Source: host `W/src-frz-a` (`W` = `~/project-offloads/future-version-20261111`), a `git archive` of
  3d700effcabe1dbf2d3ceaa3aaa469fcdfb955de (host file `FROZEN_COMMIT`). Read only. `Cargo.lock` unchanged in every run.
- Entry: `crate::process_r1_cost_probe_instruction` of `programs/r1-cost-probe` (crate `aspis_r1_cost_probe_program`).
- Features: `--features aspis`, the deployed build command (`W/out/frz-a-dev/cmd.txt`: `cargo-build-sbf
  --manifest-path .../programs/r1-cost-probe/Cargo.toml --features aspis ... -- --locked`).
- Deployment ids: the deployed build sets `ASPIS_R1_POOL_PROGRAM_ID=4hxEyoU8MC3oFMya8D8MAcvhCPhLfHKDP1Ji9byYycn1` and
  `ASPIS_R1_REGISTRY_PROGRAM_ID=9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q` (`W/out/frz-a-dev/env_exact.txt`); the
  Charon runs set the same two variables, so `option_env!` sees the deployed values.
- Overflow checks: OFF in the deployed build. The workspace `Cargo.toml` sets `overflow-checks` only for the packages
  `aspis-r1-cert-check` and `aspis-r1-cert-build`; there is no other `[profile.release]` entry, no crate sets one,
  `.cargo/config.toml` holds only an alias, and the deployed environment has no `RUSTFLAGS`. `cargo-build-sbf`
  3.1.13 adds `-C opt-level=s` and LTO flags, and no overflow flag (strings of the binary). The primary emission sets
  `CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=false` (the same value as the default). Every row of `rows.tsv` was emitted
  with overflow checks off; `rows-overflow-on.tsv` is the same table for the `on2` run.
- Resolved features (`cargo tree -e features`, same manifest and features; host target with nightly-2026-09-17 and
  SBF target `sbpf-solana-solana` with the platform tools v1.54 cargo give the same sets; files `W/x1/tree2/`):
  - `aspis-r1-cost-probe-program`: aspis, custom-heap, default, fast-kmul, fast-prepared, fast-square,
    final-pair-expansion, fold-shared, lazy-boundary, lazy-horner, merkle-in-place, merkle-single-pass, one-tx,
    pool-adapter, private-leaf-salts, tight-base, tight-weights, validated-decode
  - `aspis-r1-cost-probe`: default, final-pair-expansion, fold-shared, lazy-boundary, lazy-horner, merkle-in-place,
    merkle-single-pass, optimized-terminal, private-leaf-salts, program-build, tight-base, tight-weights,
    validated-decode
  - `aspis-statement`: pool-v1-kernel, pool-v1-pair-forest-active-mask-basis-audit,
    pool-v1-pair-forest-binary-copy-weights-audit, pool-v1-pair-forest-copy-finish-dot-basis-audit,
    pool-v1-pair-forest-copy-pattern-basis-audit, pool-v1-pair-forest-copy-selector-tensor-basis-audit,
    pool-v1-pair-forest-copy-tag-dot-basis-audit, pool-v1-pair-forest-endpoint-selector-cache-audit,
    pool-v1-pair-forest-packed-digest-audit, pool-v1-pair-forest-packed-digest-selector-tensor-audit,
    pool-v1-pair-forest-packed-range-audit, pool-v1-pair-forest-pattern-window-audit,
    pool-v1-pair-forest-semantic-factor-audit, r0
  - `aspis-core`: fast-kmul, fast-prepared, fast-square, lazy-horner, r0

  The freeze emission's statement scopes lacked three of these (`copy-pattern-basis-audit`,
  `copy-selector-tensor-basis-audit`, `packed-digest-audit`). This run uses the resolved set because it compiles the
  program crate itself.
- Target: Charon compiles for the host (x86_64-unknown-linux-gnu), not SBF. The only `cfg(target_os = "solana")` code
  on the reached path is `SolanaDigest::digest_into` in `programs/r1-cost-probe/src/lib.rs`: on SBF it calls the
  `sol_sha256` syscall, on the host `hashv`; the emission has the host branch. The global allocator and the
  heap high-water log are also SBF-only and are not on the translated path.
- MIR: `--mir built` applies to the program crate only. Charon reads the three library crates as dependencies, from
  their optimized MIR (Charon's help: "for dependencies only MIR optimized is available"). The freeze emission
  translated each library crate as the local crate, from built MIR. The body comparison below shows what this changes.

## What was run

Tools, checked by hash at the start of every run (`fv_x1_run.py`): Charon 454586e9 sha256
57aa2359bb3e9a84480f7e4802dcdc700ef05709de30ec0eb97581b3f9c5f851, charon-driver
6a6552bce70d59e041fb96a67c08294377ef16d3f77a7876fea7f1250ee37845, Aeneas 0d21a9ec
230ee9f0c4902ea3415a01960f6887e2d4c71bc82e8b4e78dfac398da657df91 (the hashes of the freeze README). Lean 4.32.0
against the L187 objects by reference (`codex-cx-replay-l187-20261109/objs` and `base_ref`), `-j1 -M7000
-DElab.async=false`, timeout 2400 s (`fv_x1_lean_one.sh`; the freeze script's 180 s fits one scope, not five).

Charon command (`runs/<run>/runs/C/charon_command.json`):

    charon cargo --preset aeneas --mir built --sysroot default
      --include core::option::Option --include core::result::Result --include core::option::_::ok_or
      --start-from crate::process_r1_cost_probe_instruction
      --include aspis_r1_cost_probe --include aspis_statement --include aspis_core
      --opaque crate::r1_pool_adapter::deployment_ids::program_id
      --opaque crate::r1_pool_adapter::deployment_ids::deployment_id
      --opaque crate::r1_pool_adapter::close_checkpoint
      --opaque crate::r1_pool_adapter::lifecycle_accounts
      --opaque aspis_core::field::_::inv
      --dest-file <run>/runs/C/out.llbc
      -- --manifest-path <src>/programs/r1-cost-probe/Cargo.toml --locked --offline --release --lib --jobs 4 --features aspis
    env: PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin RUSTUP_TOOLCHAIN=nightly-2026-09-17 CARGO_NET_OFFLINE=true
      CARGO_BUILD_JOBS=4 RAYON_NUM_THREADS=1 CARGO_PROFILE_RELEASE_CODEGEN_UNITS=2
      RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1' CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=false
      ASPIS_R1_POOL_PROGRAM_ID=... ASPIS_R1_REGISTRY_PROGRAM_ID=... (as above)
      CARGO_TARGET_DIR=W/x1/target/src-frz-a-off
    on2 only: RUSTFLAGS adds '-C overflow-checks=yes', CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true,
      CARGO_TARGET_DIR=W/x1/target/src-frz-a-on

Aeneas: `aeneas -diagnose-translation -sequential -no-progress-bar -abort-on-error -backend lean -namespace AspisX1
-dest <run>/runs/A-release/raw -subdir AspisX1 -split-files <llbc>`.

Adaptation: the verifier worker's `TP_adapt.py` (sha256 e5460b7c7900134198ad1b43e8e37e6645e2be5b47addb274982ebfb455c12de)
with `fv_x1_rules.json`, which is `TP_rules_release.json` plus one import line for `AspisTP2NewLib`. Two existing
shims are compiled first: `AspisTPNewLib` (13f0700ef54893b0fcef4741dc76ac212b66d7efdf1f11bf8af5215873a8f81a) and
`AspisTP2NewLib` (0d47d5e3a7d4f5b699e820567bffdb424fb8866985c6da442beb9aac8e138344). Every shim definition is listed in
`shims.tsv` with the Rust item it models. No new shim is used. The rules' `compact.`/`weights.` renames change only the
`Source:` paths inside doc comments in this emission (all 90 occurrences of `_root_.AspisX1.` are on `Source:` lines);
the tables read spans from the raw emission.

Why the opaque flags: the exploratory run `explore1` (no item opaque; Aeneas with and without `-abort-on-error`)
recorded the rejections listed under "Named gaps". Two flag facts:
- This Charon cannot name a method of one inherent impl: `aspis_core::field::{aspis_core::field::CM31}::inv` matches
  nothing (`charon/src/name_matcher/mod.rs`: an `Impl` pattern element against an inherent `ImplElem::Ty` is "TODO
  false"). Only `aspis_core::field::_::inv` reaches `CM31::inv`, and it also makes `M31::inv` opaque. `QM31::inv` is
  not reached.
- `--exclude ...::inv_with` with `CM31::inv` transparent leaves a dangling call; Aeneas then stops with "Internal
  error: please file an issue" at `field.rs` 391:8-391:31 (`probe2`). With `CM31::inv` opaque, `inv_with` is not
  reached, so no exclude is used.

Runs (receipts `W/receipts/<attempt>/`; one slot at a time; every scope MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0,
TasksMax 256; no memory event in any run; no swap possible inside the scope):

| Attempt | What | Exit | Wall | Peak RSS (time -v) | Scope memory peak |
|---|---|---|---|---|---|
| X1-tree, X1-tree2 | `fv_x1_tree.sh`: `cargo tree -e features`, host and SBF | 0 | 0:01.26, 0:02.21 | 78,560 kB | 143,556,608 B |
| X1-explore1 | nothing opaque; Aeneas release (exit 2, first rejection) and without `-abort-on-error` (exit 1) | 0 | 3:24.41 | 3,444,392 kB | 3,860,066,304 B |
| X1-off1 | first opaque list (CM31 pattern matched nothing; Aeneas exit 2, arrow types in `inv_with`) | 0 | 0:09.49 | 480,832 kB | 587,694,080 B |
| X1-probe2 | `--exclude _::inv_with` only (Aeneas exit 2, internal error) | 0 | 0:08.82 | 446,512 kB | 530,710,528 B |
| **X1-off2** | **primary**: overflow checks off; Charon, Aeneas release exit 0, scans, Lean | 0 | 5:41.24 | 4,713,404 kB | 3,640,287,232 B |
| X1-on2 | overflow checks on; otherwise identical | 0 | 8:15.45 | 4,741,332 kB | 3,571,056,640 B |
| X1-shimtest1, X1-off3 | a shift shim, then withdrawn (owner decision: no new std shim); off3 stopped by me during Aeneas (exit 143); not used | | | | |

Step detail (`runs/<run>/steps.txt`, `result.json`):

| Step | off2 | on2 |
|---|---|---|
| Charon | exit 0, 3.8 s (cargo cache of explore1), peak 364,976 kB, 1430 function declarations | exit 0, 69.0 s (cold), peak 726,196 kB, 1430 |
| LLBC sha256 | 7cf319b559fe83afbe331170dc1baf3253454f85032d8add9d170166b14de75e | 41bdc2b0fd4f1ba85cbb18bc91f3fc8b0d18af92b4ed4bce0c115caa4e18f55b |
| Aeneas release | exit 0, 182.5 s, peak 3,486,976 kB | exit 0, 245.9 s, peak 3,184,128 kB |
| Lean TypesExternal / Types / FunsExternal | exit 0 / 0 / 0, no error | exit 0 / 0 / 0, no error |
| Lean Funs | exit 1, 121.8 s, 42 error lines in 25 declarations, peak 4,713,404 kB | exit 1, 143.1 s, 13 error lines in 6 declarations, peak 4,741,332 kB |

The off3 LLBC, made with the same Charon configuration as off2, differs from it only in the `dest_file` option
recorded inside the file. `sorry`: none in any `Funs`. The `[Error] lines 0` in `steps.txt` is a counting defect of my
driver (the log is coloured); the rejections are in `aeneas.log`.

Hashes of every emitted file, raw and adapted, and of the LLBC files: `emission-sha256.txt`. The RAW Aeneas output
of every run stays on the host beside the adapted copy: `W/x1/runs/<run>/runs/A-release/raw/AspisX1/` (explore1:
`A-noabort/raw/AspisX1/`), so it can be compiled against another library without rerunning the tools.

## Tables

- `rows.tsv`: one row per function or constant of the four crates with a doc block in `Funs` or `FunsExternal` (the
  freeze row rule: closures, loop bodies, core-trait impl methods and type declarations are not rows; their Lean errors
  count for the owning function), plus the two named gaps not in the emission. Columns: Rust path as Aeneas names it;
  crate; file:line range; source revision; sha256 of the source lines; translates; elaborates; Lean module and
  definition name; overflow-check setting (`off` on every row); class against the pin (`TP_fntext.py` against
  `W/frz-emit/pin-c7593d23fdc`, the freeze classifier); raw pin comparison; `also_in_frza` (the letters of the freeze
  scopes whose `Funs` has a definition of the same Rust path); note (named-gap message, or why it does not elaborate).
  Source-line convention: the lines of the `file:line` column, joined with newlines and newline-terminated. That range
  is the doc comment's `Source:` range when it spans more than one line. For items of the three library crates Aeneas
  gives only the signature line; then the range runs from that line to the closing brace of the body (or the `;` of a
  constant), found by brace matching after blanking comments, strings and character literals (`fv_x1_rows.py`,
  `item_extent`).
- `rows-overflow-on.tsv`: the same table for `on2`.
- `externals.tsv`, `shims.tsv`, `not-emitted.tsv`, `compare-frza.tsv`, `overflow-diff.tsv`, `summary.json`,
  `summary-overflow-on.json`.

## Totals (off2, the deployed setting)

| Crate | Rows | Translate and elaborate | Translate only | Named gap |
|---|---|---|---|---|
| aspis_r1_cost_probe_program | 71 | 64 | 3 | 4 |
| aspis_r1_cost_probe | 206 | 196 | 10 | 0 |
| aspis_statement | 322 | 315 | 7 | 0 |
| aspis_core | 115 | 109 | 3 | 3 |
| all | 714 | 684 | 23 | 7 |

on2 (overflow checks on): 703 / 4 / 7; the 19 rows that elaborate only with checks on are all shift rows (below).

Translate, do not elaborate (off2):
- 19 rows, all from one cause: with overflow checks off Aeneas emits a Rust `<<`/`>>` as
  `Std.<T>.wrapping_shl/shr x s` with the amount `s` at its own Rust type (a literal `i32`, `usize`, `u8`); the R1
  library (and the pinned Aeneas commit's own library, `Std/Scalar/WrappingOps/Shl.lean`, `Shr.lean`) define those
  functions for a `U32` amount only. Rows: `fast_domain::fibre_point`, `multiproof::merged_level`,
  `one_tx::base_fold`, `one_tx::base_query`, `Weights::inactive_tensor`, `sampler::qm31_div_pass`,
  `one_tx::merged_keys`, `one_tx::merged_tree`, `transport::Variant::final_len`,
  `state_only_poseidon::internal_linear_lazy`, `append_level_packed_selector_tensor`, `Selectors::row`,
  `add_value_lanes`, `validate_transition`, `accumulate_endpoint_selector_tensor_basis`, `link_weight`,
  `QM31::square`, `QM31::mul`, `QM31::mul_add`. With overflow checks on, all 19 elaborate.
- `compact::expand_values`: library item missing from the old library (the `Iterator` instance of
  `core::slice::ChunksExactMut`, whose emitted definition uses the fields `zip`, `fold`, `all` that the R1 `Iterator`
  structure does not have, and `Zip` over chunk iterators). Same in on2.
- `lifecycle_init`, `lifecycle_write`, `lifecycle_finalize`: they translate; they do not elaborate. Each calls the
  opaque `lifecycle_accounts`, whose axiom returns its result with a back function (the slice holds
  `AccountInfo`, which contains mutable borrows); the `?` on it is emitted as a three-way destructuring of
  `CoreOpsTry.branch`, which the shim defines without back functions ("expected a product type, got ControlFlow ...").
  Same in on2. `pool_route::admitted` rejects their instruction tags before any account is read in the deployed
  program.

`r0::heap::filled` elaborates here (the TP rules map `alloc.alloc.Global` to the shim; the freeze core scope used the
XP rules, which do not).

## Named gaps (exact tool messages; from explore1, `runs/explore1/runs/A-noabort/aeneas.log`)

| Item | Rejection | In this emission |
|---|---|---|
| `r1_pool_adapter::deployment_ids::program_id` | Aeneas "Early returns inside of loops are not supported yet", `deployment_ids.rs` 3:0-44:1 (PrePasses.ml line 575) | not reached (only through `deployment_id`) |
| `r1_pool_adapter::deployment_ids::deployment_id` | Aeneas "Internal error, please file an issue", `deployment_ids.rs` 50:15-50:20 (interp/Interp.ml line 686) | axiom; called only by the initializers of the statics `AUDIT_POOL_PROGRAM`, `AUDIT_REGISTRY_PROGRAM`, which therefore translate as calls to an axiom |
| `r1_pool_adapter::close_checkpoint` | Aeneas "Inconsistent projection: pe PtrMetadata" on a shared borrow of `[AccountInfo]`, `r1_pool_adapter.rs` 1033:8-1033:26 (the slice pattern `let [checkpoint, base] = accounts`) | axiom |
| `r1_pool_adapter::lifecycle_accounts` | the same message, `r1_pool_adapter.rs` 251:8-251:27 (`let [target, authority] = accounts`) | axiom |
| `CM31::inv` | Aeneas "Invalid input for unop: fn_def_to_fn_ptr on aspis_core::field::{aspis_core::field::M31}::inv", `field.rs` 391:22-391:30 | axiom |
| `CM31::inv_with` | Aeneas "Arrow types are not supported yet" in the signature, `field.rs` 396:4-396:58 (symbolic/SymbolicToPureTypes.ml line 422); "Function pointers are not supported yet", 398:23-398:36 | not reached (only through `CM31::inv`) |
| `M31::inv` | no rejection: explore1 translates it | axiom, only because of the pattern limit above; its elaboration was not checked |

`CM31::inv` and `inv_with`: by the soundness lead's ruling the first-pair definitions
(`AspisR72Sampler.field.CM31.inv`, `inv_with`, branch `research`) are reused; no link was built. The frozen source
text equals the pin c7593d23fdc56fcee9a9df1628d5f63b52ac7a95 (`git show <rev>:crates/aspis-core/src/field.rs`):
lines 390-392 (`inv`) sha256 f845f645286ccf2e30b22527687ed4c306dbed5696523ac55640ffa6f43075b8 at both revisions;
lines 396-404 (`inv_with`) sha256 8f8ae1ea96a589ae88feef7e2cba53c7d01dd9b85f564d63833986c918c09232 at both revisions.

The other items of the brief's re-check list: `lifecycle_init/write/finalize` translate (see above);
`AUDIT_POOL_PROGRAM`, `AUDIT_REGISTRY_PROGRAM` translate and elaborate; `heap::uninit` and `QM31::inv` are not reached
from the entry; the four payment-relation codecs translate and elaborate.

## Derived impls and the 27 former bodiless items

In the freeze emission these were axioms because each scope included only its own crate. Here the library crates are
included, so:
- `WideExact` `Clone::clone` and `PartialEq::eq`, `WideExact::ZERO`, `ONE`, `QM31` `PartialEq::eq`, `C1_TAG`, `C2_TAG`,
  the derived `Debug::fmt` of `verifier::Error`, the three statement constants, both `is_paused`, the four codecs:
  translated, elaborate.
- Derived `Clone` that is not emitted (47, `not-emitted.tsv`): Charon translates the body but the item is not in
  Charon's `ordered_decls`. That list is rebuilt from the start points after Charon's passes
  (`transform/add_missing_info/reorder_decls.rs`, `compute_declarations_graph`); a derived `clone` of a `Copy` type
  becomes unreachable once its uses are plain copies. Aeneas extracts only listed groups. No Charon option changes
  that for an unreachable item, and no emitted definition refers to one. No option was found that emits them, and they
  are not written by hand.

## Completeness per crate (defect check 1)

Against the off2 LLBC (`not-emitted.tsv` lists every name):

| Crate | Declarations | With a body | Emitted (definition) | Opaque by flag | Not emitted: drop glue | Not emitted: derived Clone | Not emitted: other |
|---|---|---|---|---|---|---|---|
| aspis_r1_cost_probe_program | 125 | 122 | 117 | 3 | 4 (Aeneas-dropped) | 1 (Charon-unreachable) | 0 |
| aspis_r1_cost_probe | 314 | 314 | 274 | 0 | 34 (Aeneas-dropped) | 6 (Charon-unreachable) | 0 |
| aspis_statement | 535 | 535 | 442 | 0 | 60 (Aeneas-dropped) | 33 (Charon-unreachable) | 0 |
| aspis_core | 201 | 199 | 158 | 2 | 1 Aeneas-dropped, 1 Charon-unreachable | 7 (Charon-unreachable) | 32 (Charon-unreachable: 28 `r0::scalar` macro impls, `field` `pow` and `neg`, two `wide_exact` items) |

Reasons:
- "Charon-unreachable": in `fun_decls` with a body, not in `ordered_decls`.
- "Aeneas-dropped": in `ordered_decls`, not emitted. This is the known Aeneas behaviour
  (`PrePasses.simplify_trait_calls`, `keep_group`): a group of a non-local crate is kept only if a function body,
  global, trait default or explored impl refers to it. All 99 such items here are drop glue (`{Builtin}`).
- Matching is by source file and first line, plus the macro-invocation line (the `r0::domain` getters are emitted
  under the macro).

The check the lead asked for: a function called by an emitted definition with no definition and no external
declaration would show in Lean as an unknown identifier. The only unknown names in the Funs log are
`core.slice.iter.ChunksExactMut.Insts.CoreIterTraitsIteratorIteratorMutASlice` (twice, in `expand_values`). That is a
std instance which is emitted and fails to elaborate. It is not a missing declaration. No unknown name of an Aspis
crate occurs.

## Other defect checks

- Mutable-borrow type arguments under an erased region: 0 with `TP_llbc_scan.py` (over the four crates) and 0 with
  `tp3_erased_scan.py` (each crate), in off2 and on2. As the freeze README says, this Charon does not write an erased
  region there, so the scan cannot fail; it is not evidence about written-back values.
- `tp3_erased_scan.py` completeness counts only local functions, so here only the program crate (72 local
  transparent, 5 missing: 4 drop glue, 1 derived `Clone`). The per-crate table above covers the other three crates.
- Reversed mutable iterator, source search of the four crates: `sampler.rs` 62 (doc comment), 163, 178, 265
  (`#[cfg(test)]` modules) and `r0_transcript.rs:129` (`base_p_digits`, not in the emission). None is on the
  translated path. The same as the freeze run.

## Overflow-check comparison (off2 against on2)

`overflow-diff.tsv`, per function body after normalisation: 1170 Aspis bodies identical and 98 different. 97 of the
different ones differ in arithmetic only (wrapping operations with overflow checks off against checked operations
with them on). The other is one loop body that differs in local bindings. By crate: core 16, verifier 39 (38 + 1),
statement 36, program 7. Raw `Types.lean` and `FunsExternal_Template.lean` are byte-identical between the two runs.
The setting of each row is in the `overflow_checks` column (off in `rows.tsv`, on in `rows-overflow-on.tsv`).

## Comparison with the per-crate freeze emission (FRZE-frza)

`compare-frza.tsv`: for every function present in both, the X1 body at the setting the freeze scope used (on2 for
v, s, d, c; off2 for p) against the freeze body. Doc comments and Lean attributes are dropped. The namespace is
removed, local names of the freeze scope are written with the crate prefix, and `AspisXPNewLib.` is written as
`AspisTPNewLib.` (the same five definitions). The labels:

| Scope | Identical | Identical up to whitespace | Different: local bindings only | Different: constant evaluated | Different: other |
|---|---|---|---|---|---|
| v | 108 | 207 | 32 | 1 (`compact::OFF_SEMANTIC`) | 2 |
| p | 124 | 0 | 7 | 0 | 0 |
| s | 144 | 212 | 0 | 1 (`POOL_V1_PAIR_TREE_DEPTH`) | 3 |
| d | 24 | 210 | 3 | 1 (`POOL_V1_PAIR_TREE_DEPTH`) | 0 |
| c | 37 | 98 | 0 | 0 | 1 |

What the differences are:
- Local bindings only: the same called functions and constants, different temporaries (for example the freeze body
  binds a copy `let q ← ...` that the X1 body does not). In v, s, d and c this is the effect of optimized
  dependency MIR against built local MIR. In p (the same setting, off, and both built MIR) the 7 functions
  (`authenticate_invariant_release_registry`, `lane_frontier`, `decode_lane_from_pool_release`,
  `authenticate_asq8_accounts`, `emit_result`, `owned::stage2_owned`, `owned::stage2`) also differ in local bindings
  only. My reading, not checked call by call: they bind the results of library calls differently because the library
  functions now have bodies instead of axioms. This is an effect of the whole-program run, not of the overflow setting.
- Constant evaluated: the freeze body calls the constant's initializer, the X1 body holds its value, because Charon
  evaluates the constants of dependency crates.
- Other: `COPY_TAG_TERMS` (an array constant evaluated; same cause); `array_from_fn_copy` (twice; only the qualified
  name of its own loop helper differs, a naming artefact of my normaliser); the std `ChunksExactMut` iterator impl
  (X1 emits more of its methods); `r1_wire::ValidatedRecord::decode_k` (the freeze body holds an unused
  `let _ ← QM31.ZERO` that the X1 body does not); `r0::heap::filled` (`alloc.alloc.Global` against the shim name).
- Feature sets: I did not check whether any different body is gated by one of the three statement features the
  freeze scopes lacked. The kinds of difference listed above do not need a feature difference to explain them.

## What is NOT translated, and why

- Named gaps: `deployment_ids::program_id`, `deployment_ids::deployment_id`, `close_checkpoint`,
  `lifecycle_accounts`, `CM31::inv`, `CM31::inv_with` (tool rejections above) and `M31::inv` (opaque by the pattern
  limit).
- Translate without elaborating: the 19 shift rows (off setting only), `compact::expand_values`, the three lifecycle
  handlers.
- The SBF-only `sol_sha256` branch of `SolanaDigest::digest_into` (host branch translated).
- SDK and runtime functions: no models; listed in `externals.tsv`. The 5 rows classed "Solana runtime" are the SDK
  functions that are syscalls on SBF (`sol_log`, `set_return_data`, `Clock::get`, `create_program_address`,
  `hashv`); in this host build their SDK host code is what Charon sees, and it is not translated.

## Not checked

- The elaboration of `M31::inv`'s body (opaque here).
- Whether any body that differs from the freeze emission is gated by one of the three statement features the freeze
  scopes lacked.
- Lean against the pinned Aeneas commit's own library (worker X3).
- Whether a different Charon version can single out `CM31::inv`.

## Rerun

On the host, in `W/x1`:

1. `bash bin/fv_x1_tree.sh` inside `fv_slot.sh` (resolved features).
2. `bash bin/fv_x1_emit.sh $PWD/bin/fv_x1_cfg_off.json <label> 5400` (one slot; about 6 minutes with a warm cargo
   cache, 8 minutes cold), and the same with `fv_x1_cfg_on.json`.
3. `python3 -I bin/fv_x1_rows.py runs/<off label> runs/<on label> <table dir>` (reads only; about 7 s).

Scripts (this directory's `../host/`): `fv_x1_run.py`, `fv_x1_emit.sh`, `fv_x1_lean_one.sh`, `fv_x1_rows.py`,
`fv_x1_tree.sh`, `fv_x1_lean_test.sh`, `fv_x1_rules.json`, configs `fv_x1_cfg_explore.json`, `fv_x1_cfg_probe2.json`,
`fv_x1_cfg_off.json`, `fv_x1_cfg_on.json`. The rows script imports the freeze driver `fv_frz_emit_run.py` (row rule,
classifier) read only. sha256 (as committed): `fv_x1_run.py` 66e308b4dd5b643a94e3ed41895f8d66ae2b1c93df529789b7d8aa4dcff6f174
(ran on2; off2 ran the version 40c47cec5057f7f8492f939bfcdfc1ae9491a47f0216ffce06b1fc7b1ab5bda4, which differs only in
the shim-directory lookup added later), `fv_x1_rows.py` 8ba0b78566b8b7187b284ce48bea9470b9ce97328b5edcce5552b84f2009f286,
`fv_x1_lean_one.sh` 998e357cb1769eb72145ea7ae85ccd78af5a0f5a173416224f66702a10722e12, `fv_x1_rules.json`
1c53f0ff5ff18c24d65f2b505b7682999f8ad975da3ab7be0150d57ba7829883, `fv_x1_cfg_off.json`
0fc43c5146d8d0f479d414d9e07b7bd283ea23e1bf27721c1e6e9146f1400824 (= off2 `config.json`), `fv_x1_cfg_on.json`
e7a60f789dc85090df48c2b104e6257059fe45f16a434136e71dd7a8bcedcaa8 (= on2 `config.json`). The withdrawn shift shim `AspisX1ShiftLib.lean` (sha256
581258ce104c664ebbdfa3e05e8c74cd137c50ec4aefe6b0842edcdc03a083d0) is not part of this record.
