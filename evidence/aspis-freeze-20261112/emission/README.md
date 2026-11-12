# Aspis freeze: release-style translator emission of the on-chain path

Status: target not yet established. This is a tool record. It says which on-chain-path functions the
Charon and Aeneas tools translate, and whether the emitted Lean elaborates against the R1 (L187)
library. Nothing in it is a proof, and a translated, elaborated function is not a verified function.

## Tables and the trees they come from

| Table | Tree | Source revision | Run |
|---|---|---|---|
| `rows-cand1.tsv` | host `W/src-cand1` | 33e2d8475bc (commit), host file `SRC_CAND1_COMMIT` | attempt `FRZE-cand1`, label `cand1` |
| `rows-frozen.tsv` | host `W/src-frz-a` | 3d700effcabe1dbf2d3ceaa3aaa469fcdfb955de (host file `FROZEN_COMMIT`) | attempt `FRZE-frza`, label `frza` |

(`W` = `~/project-offloads/future-version-20261111` on the build host.)

Columns: scope; run (`v` verifier crate, `p` program crate, `s` statement semantic side, `d` statement and
account decoders, `c` aspis-core); function (Rust path as Aeneas names it); file:line (as in the emission's
doc comment); translates; elaborates; class; pin_text (the raw function-text comparison with
c7593d23fdc); note (the reason, for a named gap).

## What was run

There is one script, `host/fv_frz_emit.sh <source-dir-name> <label> <program-features> <verifier-features>`,
which uses `fv_frz_emit_inner.sh`, `fv_frz_emit_run.py` and `fv_frz_emit_lean_one.sh`, and reads the per-tree
config `host/config/<source-dir-name>.json`. The config holds the roots, opaque items, includes, the statement
and core feature sets, the named gaps and the list of pass rewrites. The script itself names none of them.
Everything runs in ONE `fv_slot.sh` scope (MemoryHigh 6G, MemoryMax 8G, no swap, TasksMax 256), and only one
slot was used at a time.

| Run | Arguments | Exit | Wall (inside the scope) | Peak RSS (time -v) | Scope memory peak | Memory events | Slot |
|---|---|---|---|---|---|---|---|
| `FRZE-cand1` | `src-cand1 cand1 <deployed program list> <TP-C70 verifier list>` | 0 | 11:18.01 | 3,586,392 kB | 4,084,695,040 bytes | none (oom 0) | 3 |
| `FRZE-frza` | `src-frz-a frza aspis aspis` | 0 | 13:33.92 | 3,594,152 kB | 3,631,714,304 bytes | none (oom 0) | 2 |
| `FRZE-cand1-rows`, `FRZE-cand1-rows2`, `FRZE-frza-rows2` | `fv_frz_emit_run.py rows-only` (table rebuild, reads only) | 0 | under 1 s each | about 25 MB | | | |

Receipts: `runs/<label>/receipt/`. Steps with per-step exit codes and wall times: `runs/<label>/steps.txt`. Every
hash: `runs/<label>/result.json`.

Per scope, the run does the following:

1. Charon, second pair, with the workers' command line and environment (TP_charon.py / XP_charon.py: `--preset
   aeneas --mir built`, `--release --lib --locked --offline`, nightly-2026-09-17). The source tree is read only.
   Each tree and scope gets its own cold cargo target directory under `W/frz-emit/target`. `Cargo.lock` was
   unchanged in every run.
2. Aeneas, second pair, WITH `-abort-on-error`. It exited 0 in all ten scopes, so the run without the flag was
   never needed.
3. Scans:
   - `TP_llbc_scan.py` (the verifier worker's) on the scope's crate: completeness by span, and mutable-borrow
     type arguments under an erased region;
   - the same tool on the other crates in the LLBC, for non-local functions with a body that were not emitted;
   - `tp3_erased_scan.py` (the core worker's, the version whose hash the core note records);
   - a search of the scope's crate sources for a reversed mutable iterator.
4. Lean 4.32.0 against the L187 objects, by reference. The shims `AspisXPNewLib`, `AspisTP2NewLib` and
   `AspisTPNewLib` are compiled first into the run's own `lean-out`. Then each scope's four modules are adapted
   with that worker's tool and rules (verifier and program: `TP_adapt.py` + `TP_rules_release.json`; statement
   semantic: `XP_adapt.py` + `XP_rules_tp2.json`; decoders and core: `XP_adapt.py` + `XP_rules_newlib.json`) and
   compiled one at a time. The command is the workers' `fv_lean_one.sh`, with only the source and object
   directories changed.
5. `TP_fntext.py` compares the four crates' functions with the pin tree `W/frz-emit/pin-c7593d23fdc`, made by
   `git archive c7593d23fdc` of the four crate directories.

Scopes (copied from the workers' specs; the five runs are reported as four scopes):

| Scope | Worker spec | Roots | Features |
|---|---|---|---|
| verifier | TP-C70 | the one-transaction entry without the observer (`fused::verify_summed_format_unobserved` / `one_tx::verify_unobserved`), `verifier::checkpoint_size` | argument 4 |
| program | TP-C71 | `process_r1_cost_probe_instruction`; the named gaps opaque | argument 3 |
| statement (semantic) | T2-C07 | `Public::terminal_qm31`, `Public::public_bytes`; aspis_core field, hiding and prefix included, wide_exact opaque | from the config |
| statement (decoders) | T3-C12 | 27 decoder and validator roots; the four payment-relation codecs opaque | from the config |
| core | T3-C14 | 61 roots; field `inv` opaque, `CM31::inv_with` excluded, `heap::uninit` opaque | from the config |

The `src-frz-a` config differs from `src-cand1` in two places only. The verifier root is renamed. The aspis-core
feature names lose the `future-` prefix in the statement-semantic and core feature sets.

Tool binaries, checked by hash at the start of every run:
- Charon 454586e9: sha256 57aa2359bb3e9a84480f7e4802dcdc700ef05709de30ec0eb97581b3f9c5f851; charon-driver sha256
  6a6552bce70d59e041fb96a67c08294377ef16d3f77a7876fea7f1250ee37845.
- Aeneas 0d21a9ec: sha256 230ee9f0c4902ea3415a01960f6887e2d4c71bc82e8b4e78dfac398da657df91.

Worker tools, copied unchanged into `W/frz-emit/bin/worker` (sha256):
- `TP_adapt.py` e5460b7c7900134198ad1b43e8e37e6645e2be5b47addb274982ebfb455c12de
- `TP_llbc_scan.py` 6a5bc6f1d7499373fcb802d33867d3e8707a2c6994bdc5ced9522b9eb8e42c71
- `TP_errmap.py` 9aa7f50678af476cfdca0f69dc1fc374aa0a67d8dd4ec5ce5c6ff60f5eb08015
- `TP_rules_release.json` 624e36d305e21f36f193944494d3398d1256efe99724716a7f5b25ecdba49f48
- `TP_fntext.py` 8b002b20352e61226fd501641f6b564b11efb19126d240ca60b10bcd61140290
- `XP_adapt.py` 077ae941f172504f6092fc3a4b90ac7fe58c336b20dc3384c1986d9b8f6f7ad3
- `XP_rules_tp2.json` e7dbbe5411c9d6066a7ec910ea1f73c40304fbe8a3e85e05cf8f64c77e2b200b
- `XP_rules_newlib.json` ebc830c13d90b64f3b3801c19fcef3f207ac09a6e9f91c3cc670564241988ae2
- `tp3_erased_scan.py` ba40e0671ba039b46d6b1ff751c24b31841dd04c4f832f6921415cebc6a3f45d. This is the repository
  copy. The host's `tp3-xp` copy differs; its hash is 2192a7ec8fa28d6ec92ca5323827d3d09bbdbe881f70e807ea304486beab269f.

Shims:
- `AspisXPNewLib` bc90debcc3306e8f1e486b19546962391ea00376e2410d189e2f58db6ce1f841
- `AspisTP2NewLib` 0d47d5e3a7d4f5b699e820567bffdb424fb8866985c6da442beb9aac8e138344
- `AspisTPNewLib` 13f0700ef54893b0fcef4741dc76ac212b66d7efdf1f11bf8af5215873a8f81a

All three compiled with exit 0 in both runs.

My scripts (sha256):
- `fv_frz_emit.sh` 7a21df10696baab6ee9932b6a9197a0758f14b7e3054140675aa2191ae3d08f3
- `fv_frz_emit_inner.sh` 4c7ed3860b5f0e1f9eb097e8d1314b3b602835f1056c33392354ef3e5fe0a228
- `fv_frz_emit_lean_one.sh` 9456de89c301097968c041b1256f7b6cf7d51275e2d16f6cc12f24a589c1c4b1
- `fv_frz_emit_compare.py` fddb454441380d5d4ca8f444ee6b7ec43b7d9bbe097698c73d35a2b48a7425eb
- configs: `src-cand1.json` d3b2b0c3ce616407e7496984311311b2bd99754b32f1b2d1035893672f6ca017,
  `src-frz-a.json` 8c25560a58e164a61cf774294fc505f6be2b267a555775dcdaf0466deccdba18.

`fv_frz_emit_run.py` exists in three versions:
- a60de8df5d850d6eb58fef0680eccbaed1ed28f40e3b8c6d13fd34a1beaf7aa7 ran `FRZE-cand1`;
- e3679a00b815d5c5ddcc3ca5b231203f6aa5a1d49af9b2a8d096e0c157a8359a ran `FRZE-frza`;
- 9a9e2495dbe58889b72fd5e046285bd3a1a082b011f8bdc53c240a0c714b134f is the final version. It rebuilt both
  tables (`rows-only`).

The two edits touch only the table builder (`rows_only`); the tool runs are untouched. The first edit fixed the
derived-impl pattern of the defect summary. The second fixed the recovery of source paths that the workers'
adaptation rule 3 rewrites inside doc comments (`crates/.../src/_root_.AspisTPv.compact.rs`). Before it, 44
`compact.rs`/`weights.rs` rows had the class "not compared". Both published tables come from the final version.

### Emission hashes

LLBC sha256:

| Scope | src-cand1 | src-frz-a |
|---|---|---|
| v | a37858b332de0df728e73a443ddc7a442aa4aa11a048b7853badaaa4727c3354 | 5543aedc99b862d359ad7060ab9b4a39ce45148eddc3bca62e246327f51a5840 |
| p | edcdebd869bbc971b13337b79d24f57bbdf5b89e6cda207112e7baa66d9b6dd0 | c685c0fab1288c6250936e2c36ef32775dcfa05caeafa1826e615890242c8f4a |
| s | 81f45cdb71f3424d69d15cecb55558cb9ef76ffd8e5a2f7bb70d16f263344ffc | 70e577aa7a8ff007ae4d6023d0eacf93655b33d741805ea3631c4440d4bac1f8 |
| d | 6fb7ea0a825559dac076daaa0904e66a3fc7e2e3e12ce9048494339556761942 | 9dfbf357652b4b808b1ae0f2ac1f3f59cbe7079378970e9bc0a1edec43046f04 |
| c | f74067d66c20b98c29c309e67aff424d118d96538e98e17f900add66b93b020d | 96386ad96d8d0ff240258ca4100902c3686e7293990e522e2da2e2c436012b5e |

The LLBC files contain source paths and spans, so they differ between trees.

Function declarations in the LLBC: v 493, p 297, s 400, d 322, c 253, the same in both trees. The verifier and
program counts equal the workers' TP-C70 and TP-C71.

Emitted `Funs.lean` sha256:

| Scope | src-cand1 | src-frz-a | Worker's release emission |
|---|---|---|---|
| v | 0fc89ebab8b0a1834d873f06bd17374d1985ea85f46bcf074b532a3426183d7c | 06757cf5bd33c6410f1f629a4765d46a6a137a3be53ec64bbda996cf7f2a57b3 | TP-A70vR: 0fc89ebab8b0a1834d873f06bd17374d1985ea85f46bcf074b532a3426183d7c |
| p | c6122df75ff7645203c1fa70e9adbd2c112bfceb4ed0bb443dc52c42b3dfc6e4 | 147043131049b2e5af683f799f57697e530ceddc51a3b7a10809913db6754f6d | TP-A70pR: c6122df75ff7645203c1fa70e9adbd2c112bfceb4ed0bb443dc52c42b3dfc6e4 |
| s | 4b656a0b0fee8bfe84a18bfe9031dcefb94f643c71ac7e641809d6a50ecf8eb2 | 4b656a0b0fee8bfe84a18bfe9031dcefb94f643c71ac7e641809d6a50ecf8eb2 | T2-A07: 4b656a0b0fee8bfe84a18bfe9031dcefb94f643c71ac7e641809d6a50ecf8eb2 |
| d | 753062984aca66a33fe527bc04400f65d7856ff7d1269b6c278e056ac443a8c9 | 753062984aca66a33fe527bc04400f65d7856ff7d1269b6c278e056ac443a8c9 | T3-A12: 753062984aca66a33fe527bc04400f65d7856ff7d1269b6c278e056ac443a8c9 |
| c | 84655194872dc91e3b5f64987e37a12be10f60ec1755dc18dbe46e5b02f092f4 | 84655194872dc91e3b5f64987e37a12be10f60ec1755dc18dbe46e5b02f092f4 | T3-A14: 84655194872dc91e3b5f64987e37a12be10f60ec1755dc18dbe46e5b02f092f4 |

On `src-cand1` all five `Funs.lean` are byte-identical to the workers' own release emissions. On `src-frz-a`,
statement and core are byte-identical to both. Verifier and program differ, as the renames require: module paths
and names inside the emitted Lean, and the removed experiment variants.

Lean, both trees:
- verifier `Funs`: exit 1, 9 error lines in 3 declarations, the same as TP-E70;
- program, statement semantic and decoders `Funs`: exit 0, no error;
- core `Funs`: exit 1, one error (`r0::heap::filled`, unknown `alloc.alloc.Global`), the same as T3-L14;
- every `Types`, `TypesExternal` and `FunsExternal`: exit 0 (the decoder run emits no `TypesExternal`, as T3-A12);
- no `sorry` in any `Funs`.

## Totals (identical for the two trees)

Rows: one per function or constant of the scope's crate with a doc block in `Funs` or `FunsExternal`. Closures,
loop bodies, core-trait impl methods and type declarations are not rows; errors in loop bodies and closures
count for their function. Applied to the workers' own emissions, this rule gives exactly the verifier worker's
257 rows and his 250 / 1 / 6.

| Scope | Rows | Translate and elaborate | Translate only | Do not translate | Named gaps | Opaque, not a named gap |
|---|---|---|---|---|---|---|
| verifier | 200 | 199 | 1 (`compact::expand_values`) | 0 | 0 | 0 |
| program | 57 | 51 | 0 | 0 | 6 (`close_checkpoint`, `lifecycle_init/write/finalize`, `AUDIT_POOL_PROGRAM`, `AUDIT_REGISTRY_PROGRAM`) | 0 |
| statement | 287 (290 over its two runs; 3 constants in both) | 283 | 0 | 0 | 0 | 4 (the payment-relation codecs, opaque in T3-C12) |
| core | 122 | 116 | 1 (`r0::heap::filled`) | 0 | 3 (`CM31::inv`, `CM31::inv_with` excluded, `r0::heap::uninit`) | 2 (`M31::inv`, `QM31::inv`: opaque only through the `_::inv` pattern, as in T3-C14) |
| overall | 666 | 649 | 2 | 0 | 9 | 6 |

Classes, `src-cand1`:

| Scope | R1 text identical | Identical under an added cfg | Reshaped in the pass | Aspis-only new gate | Changed against the pin, not a pass rewrite | Named gap | Needs library models |
|---|---|---|---|---|---|---|---|
| verifier | 109 | 2 (`EbyKDot::push`, `validate_record_fields`) | 8 | 81 | 0 | 0 | 0 (see below) |
| program | 39 | 1 (`process_r1_cost_probe_instruction`) | 2 | 9 | 0 | 6 | 0 |
| statement | 273 | 0 | 8 | 9 | 0 | 0 | 0 |
| core | 109 | 0 | 1 | 5 | 3 (`QM31::mul`, `QM31::square`, `PreparedQm31Multiplier::mul`: the fast kernels) | 3 | 1 (`heap::filled`) |

On `src-frz-a`, the verifier has 111 identical and 0 identical under an added cfg; every other cell is the same.

"Reshaped in the pass" is a regular-expression list in the config:
- the verifier batch: `canonical_scan`, `wide_view`, `claims`, `Prepared::new`, `QueryGeometry::for_range`,
  `prepared_claim`, and the lead's sampler rewrites `low_base_p_digits` and `add_small_base_p`;
- in the adapter: `authenticate_asq8_accounts`, `decode_lane_from_pool_release`;
- the three statement and five decoder rewrites;
- `WideExact::to_le_bytes`.

It applies only to a row whose text changed against the pin. `base_lanes_tight` is in `fused.rs`/`one_tx.rs`,
which does not exist at the pin, so it counts as an Aspis-only new gate. Fewer than the verifier note's eleven
functions are "identical under an added cfg" because the rows cover only the functions that the deployed
emission reaches.

`compact::expand_values` keeps the class "R1 text identical to the pin". My automatic library rule requires
every Lean error to be a missing-name error. This one also has a consequential "expected a product type, got
Zip". By the verifier note (section 6), it is the library-models case.

## Comparison with the three notes

The notes' own release emissions (TP-A70vR/pR with Lean TP-E70, T2-A07 with T2-L07b, T3-A12 with T3-L12,
T3-A14 with T3-L14) were turned into rows by the same rule (`ref/ref-<run>.json`, made with
`fv_frz_emit_run.py rows-ref` from the workers' adapted Lean, whose hashes match their receipts). On `src-cand1`:

| Run | Worker rows | Rows now | Same outcome |
|---|---|---|---|
| v | 200 | 200 | 200 |
| p | 57 | 57 | 57 |
| s | 131 | 131 | 131 |
| d | 159 | 159 | 159 |
| c | 121 | 122 | 121 |

Every row the notes report as translating and elaborating still does. No row is lost, and no outcome changed.
The only difference is the added row `CM31::inv_with`, which the core run excludes. The config adds it as a
named gap so that it appears in the table. File: `compare-cand1-vs-worker-emissions.json`.

The notes' counts against this run:
- Verifier note: 257 rows, 250 / 1 / 6. Same. Completeness: 270 functions with a body, 10 not emitted (derived
  `Clone` and drop glue) for the verifier crate; 89 and 4 (drop glue) for the program crate. Same.
- Statement note: Funs elaborates with no error and no `sorry`. Same. The note's "85 statement functions" counts
  differently: this table's 131 `s` rows include constants and helper functions.
- Core note: the decoders elaborate (same). Core Funs fails only on `heap::filled` (same). Not emitted: the
  derived `Clone` of 8 types, the same 8 by `tp3_erased_scan.py`.

## Frozen tree against `src-cand1`, through the rename map

`compare-frozen-vs-cand1.json`; map `evidence/future-version-20261111/host/fv_fz_rename_map.tsv`, entries of kind
fn and mod. Both tables have 669 rows. 667 rows are identical in translates, elaborates and class once the old
names are written with the map. No row is in one table only; that includes the 44 `fused` → `one_tx` rows, of
which `fused::summed_format` is now `one_tx::format`. Two rows differ, both in class only:

| Function | src-cand1 | src-frz-a | Cause |
|---|---|---|---|
| `fast_pairing::EbyKDot::push` | identical under an added cfg | R1 text identical to the pin | the undeployed `future-lean-dot` variant and its `#[cfg]` were removed; the pinned text remains without an attribute |
| `r1_wire::validate_record_fields` | identical under an added cfg | R1 text identical to the pin | the same, for `future-lean-parse` |

Translates and elaborates are the same on every row. No deployed row existed only under a removed feature, so
no row is gone.

## Defect checks (identical results on both trees)

- Silent omission of non-local declarations (core note, section 4). There is no non-local function with a body
  that went unemitted in the verifier, program or decoder runs. In the statement-semantic run, 3 non-local
  functions were not emitted, all derived `Clone::clone` of aspis_core types (`state_only_prefix.rs:1628`,
  `field.rs:254`, `field.rs:441`). The core scope is emitted as its own crate, as the core note requires, so the
  aspis_core functions are rows there.
- Derived `Clone` / `eq` not emitted. All local omissions are derived `clone` or drop glue (`{Builtin}`):
  verifier 10, program 4, statement semantic 9, decoders 27, core 6.

  In the core run, `TP_llbc_scan.py` also lists `r0::domain::{impl}::get/new` at `domain.rs:24-26`. These are
  macro-generated. Their emitted definitions carry the macro definition's lines (11, 18), so the span match
  misses them. They are emitted, and they elaborate: six rows `FibreIndex`/`SlotIndex`/`InitialIndex`
  `::get`/`::new`. `tp3_erased_scan.py`, which also matches macro-invocation lines, reports 8 for core, all
  `Clone`.

  No Lean error names a missing `clone` or `eq`. The only unknown-name errors are the library items of
  `expand_values` and `heap::filled`.
- Reversed mutable iterator write drop:
  - Mutable-borrow type arguments under an erased region: 0 in every scope with both scans. As the verifier note
    says, this pair's Charon never writes an erased region there, so the scan cannot fail here. It is not
    evidence about written-back values.
  - The source search finds `iter_mut().rev()` only in `sampler.rs` lines 62, 163, 178 and 265, and in
    `r0_transcript.rs:129`. Line 62 is a doc comment. Lines 163, 178 and 265 are in `#[cfg(test)]` modules
    (from line 153 on). `r0_transcript::base_p_digits` (line 129) is not in any emission: it is not linked,
    as in the core note.

## Rerun on another tree

1. Write `W/frz-emit/config/<tree>.json`. Copy the last one; change roots and feature names if the tree renames
   them.
2. Run `bash W/frz-emit/bin/fv_frz_emit.sh <tree> <label> <program features> <verifier features>`.
3. Run `fv_frz_emit_compare.py rename` on the two `rows.tsv` with the rename map.

The run takes 11 to 14 minutes in one slot, plus the wait for a free slot (the frozen run waited about 7
minutes). The cargo builds are cold for each tree.

## Not done, and things to note

- The four payment-relation codecs (`decode/encode_pool_v1_{private_transfer,withdrawal}_public_v1`) are opaque
  in the decoder scope, as in T3-C12. No release-style emission covers them. The statement note's exploratory
  T2-C03 run reports Aeneas errors in that file only in witness and prover functions. They are the one part of
  the reached statement code without a release-style row outcome.
- `M31::inv` and `QM31::inv` are opaque only through the core scope's `_::inv` pattern. The core note's
  non-aborting run T3-A09 emits them, and they elaborate there; that run was not repeated.
- The first tool pair was not run. `CM31::inv` and `CM31::inv_with` remain settled first-pair gates.
- Nothing here is proved: no Lean statement about any emitted definition, and no source-to-model refinement.
