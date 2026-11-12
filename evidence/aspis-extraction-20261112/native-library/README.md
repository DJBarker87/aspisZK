# Native Aeneas library: set-up, raw-emission probe and port size (task X3)

Status: target not yet established. This is a tool record. Nothing in it is a proof; an elaborated or compiled
module is not a verified one.

`W` = `~/project-offloads/future-version-20261111` on the build host. Host outputs are under `W/x3/`.

History: the first pass stopped at 31 GB free, under the 60 GB floor, and recorded only static results. The lead
then freed space (76.8 GiB reported) and the stages were run as below. The static tables of the first pass are
kept (`probe-static-library-refs.tsv`, `shim-items.tsv`); the compile results supersede the statements that
were marked unchecked there.

## Stage A: toolchain and native library (built)

| Step (attempt) | Exit | Wall | Peak RSS (time -v) | Scope memory peak | Memory events |
|---|---|---|---|---|---|
| elan install `leanprover/lean4:v4.36.0-rc2` (outside a slot; a download) | 0 | 30 s | | | |
| `lake exe cache get` (`X3-A-cache`) | 0 | 1:55.53 | 1,022,396 kB | 6,443,696,128 B | high 1655, max 0, oom 0 |
| `lake build Aeneas AeneasMeta` (`X3-A-build`) | 0 | 7:59.89 | 4,509,164 kB | 4,238,536,704 B | none |

- Lean 4.36.0-rc2, commit b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a (Release); Lake 5.0.0-src+b35cb10.
- Package revisions as checked out (`stageA-package-revs.txt`) equal the manifest for all nine packages; the
  manifest, toolchain and lakefile hashes were unchanged after the cache step.
- The cache step downloaded 9,081 files into `W/x3/mathlib-cache` (`MATHLIB_CACHE_DIR`; the shared
  `~/.cache/mathlib` was not used). The build log names no Mathlib module as built; the 3,591 build jobs that
  compiled are Aeneas and AeneasMeta modules. No cold Mathlib build.
- The "high 1655" events are throttling at MemoryHigh 6G during cache decompression; there was no OOM and no
  swap.
- Both slots ran with Lean and Lake on the slot's four cores (`slotbin/taskset --cpu-list`, `LEAN_NUM_THREADS=4`).
- Disk: free 77 GiB at start, 74 after the toolchain, 66 after the cache, 65 after the build (`stageA-df.txt`).
  `.lake` 8.05 GB (packages 7.3 GB, build 434 MB), cache 466 MB, `~/.elan/toolchains` grew from 8,768,636 kB to
  11,953,820 kB.
- Script `host/fv_x3_stageA.sh` (sha256 daf06c02444dd1c398c48bc6f3823011b0bd2d37bf1ed5421adb4980fd166364).

Source used: the archive kept beside the binaries,
`codex-pc-prov-p4x-20261110/PCWH_T004_out/aeneas-exact-source.tar.gz`, sha256
87f5f1310e5049cf2299069e6e2b7d9f30377703ea2cb5e0ba3eed3853d4e86d. Only `backends/lean` was extracted, into
`W/x3/aeneas-src/backends/lean` (275 `.lean` files, 2.8 MB).

How the source matches the binary: `PCWH_T004_out/receipt.json` (exit 0) records three things.
- `aeneas_archive_sha256` is this same hash.
- `aeneas_revision` is 0d21a9ec7bbbb110110cacc14464a47fd71c8705, which `pair-version.txt` also prints.
- `sha256_aeneas` is 230ee9f0c4902ea3415a01960f6887e2d4c71bc82e8b4e78dfac398da657df91, the binary hash the
  emission README checks at every run.

The archive has no `.git`, so the commit is known from the receipt, not from git. Every Aeneas source file whose
hash a shim header cites has the same hash in this extracted tree (nine files, listed in `shim-items.tsv`).

Read from the extracted tree:

| Item | Value |
|---|---|
| `lean-toolchain` | `leanprover/lean4:v4.36.0-rc2` (sha256 414acabc0b69c985a83eb7015af2317f0df08f7513779d512945456f8eedfdd9) |
| `lake-manifest.json` sha256 | 12fb593d2fe949112f0db995ea6648dd0a8521ed1951005839942ab084eb3364 |
| `lakefile.lean` sha256 | 784d5c0d761f6d4d246c03483b60a9dd9d9a926b0c0bcba448aff4e6daf5ffac |
| mathlib | 9d581dfff2e41de989072ea63abf3daf69311520 (inputRev v4.36.0-rc2) |
| plausible | 129d1ba9a16bc0660f46c79e9fb041ef5d5d80de |
| LeanSearchClient | c61286b7b63cbfd563b28e11e81d0a18233a044a |
| importGraph | b8cc5dd0a36233b88a6ed5a7dbf1207d09338c60 |
| proofwidgets | 16259c0d07d61ee37d999d05b5cf96338b8daa11 |
| aesop | 7d11bfa88558f8d3d90afdf6bd877ed70001498d |
| Qq | b0256621cb88178e9ad932a53633077b3029e621 |
| batteries | d4c39b228d4a06f3b00748c2c445a7b9f056a6e3 |
| Cli | c09cb1e4f1e6e1c231a1175a12b681b075054a1b (inputRev v4.36.0-rc2) |

The soundness lead's report that the toolchain is v4.36.0-rc2 agrees with this file.

## Stage B: raw emission probe

The raw Aeneas output was kept by the frozen run. For scope X it is in
`W/frz-emit/frza/runs/A-X-release/raw/<namespace>/`, with namespaces `AspisTPv`, `AspisTPp`, `AspisTP2g`,
`AspisTP3stmt` and `AspisTP3core`. Each `Funs.lean` has the raw sha256 named in the adapted copy's header and in
the emission README:
- v 06757cf5bd33c6410f1f629a4765d46a6a137a3be53ec64bbda996cf7f2a57b3
- p 147043131049b2e5af683f799f57697e530ceddc51a3b7a10809913db6754f6d
- s 4b656a0b0fee8bfe84a18bfe9031dcefb94f643c71ac7e641809d6a50ecf8eb2
- d 753062984aca66a33fe527bc04400f65d7856ff7d1269b6c278e056ac443a8c9
- c 84655194872dc91e3b5f64987e37a12be10f60ec1755dc18dbe46e5b02f092f4

No regeneration was needed.

**Compile result** (attempt `X3-B-probe`, one slot, exit 0, wall 2:37.67, peak RSS 2,155,504 kB, scope peak
1,147,518,976 B, no memory events; script `host/fv_x3_probe.sh` sha256
08bcdc44f9ffde91303aee1acd88800bb4078524c27ec64955b123865fea60c6). The raw files were byte-copied. Each
`*External_Template.lean` was copied to the file name its siblings import (`<ns>/FunsExternal.lean`,
`<ns>/TypesExternal.lean`): a rename, no content edit. No shim, no rule, no other edit. Lean 4.36.0-rc2,
`-j1 -M7000 -DElab.async=false`, against the stage A objects.

| Scope | TypesExternal | Types | FunsExternal | Funs | Funs errors | Causes |
|---|---|---|---|---|---|---|
| v verifier | 0 | 0 | 0 | 1 (0:50.88, 2.16 GB) | 50 | (1) 4, (2) 27, (3) ok_or 12, mut-iter 3, recdepth 2; 2 consequential |
| p program | 0 | 0 | 0 | 1 | 13 | (3) line-break 10, ok_or 3 |
| s statement semantic | 0 | 0 | 0 | **0** | 0 | none |
| d decoders | (none emitted) | 0 | 0 | 1 | 1 | (3) ok_or 1 |
| c core | 0 | 0 | 0 | 1 | 1 | (3) ok_or 1 |

Every `Types`, `TypesExternal` and `FunsExternal` compiles unchanged. The statement-semantic `Funs` compiles
unchanged with no error. Lean reports one error per failing declaration in these files (a `do` block stops at its
first error), so the counts are declarations; the pattern-site counts are given per cause. `probe-errors.tsv`
has one row per error (scope, line, declaration, Lean code, cause, Rust path or name, message); classifier
`host/fv_x3_probe_errors.py`.

Causes:

- **(1) library item absent from the native library.** The verifier emits an `impl_def` for
  `core::iter::traits::iterator::Iterator` on `core::slice::iter::ChunksExactMut` (Funs line 45) with the trait
  methods `zip`, `fold`, `any` and `rev` as structure fields. The native `core.iter.traits.iterator.Iterator`
  structure has only `next`, `step_by`, `enumerate` and `take` (`Std/Core/Iter.lean:93`; its comment says adding
  `rev` "leads to a circularity"). Four errors. `ChunksExactMut` itself is not native; the emission's own template
  declares it as an axiom.
- **(2) name clash.** Without the old rules, a binder named `compact` (15 errors, in `compact::check_values`,
  `expand_semantic`, `expand_semantic_loop`, `expand_values`) and a binder named `weights` (12 errors, in
  `weights::factored_s2_libra_weights` and its loop) shadow the modules `compact` and `weights`: Lean resolves
  `compact.CodecError` as field access on the local `compact : Slice U8` ("The environment does not contain
  `Aeneas.Std.Slice.CodecError`") and `weights.PERM` as field access on `weights : Array WideExact 4`. The
  shadowing is not resolved by the native toolchain.
- **(3a) `Option::ok_or` purity.** The emitter writes `lift (core.option.Option.ok_or o e)`, treating `ok_or` as a
  pure function; the native library of the same Aeneas commit declares it as returning
  `Result (core.result.Result T E)` (`Std/Core/CoreOption.lean:24`). The doubly wrapped value fails at the next
  `core.result.Result.Insts.CoreOpsTry.branch`. 17 errors; 30 `lift (core.option.Option.ok_or` sites in the raw
  `Funs` (v 18, p 3, d 8, c 1, s 0). The old shim `AspisTPNewLib`/`AspisXPNewLib` defined `ok_or` as pure
  (`core.result.Result T E`), although its header names `Std/Core/CoreOption.lean` with the same sha256 as the
  native file, which returns `Result`. The shim therefore matched the emitter, not the file it cites.
- **(3b) emitter line breaks.** In the program adapter, `r1_pool_adapter::owned::authenticate_invariant_release_registry`
  is emitted with applications broken over lines at the emitter's indentation limit (a deeply nested `if`
  chain at column 68), which Lean parses as separate terms: 10 errors in that one declaration. The old pipeline
  had the rule `@join-broken-applications` for this.
- **(3c) recursion depth.** `fast_domain::TABLE_A` and `TABLE_B`, 512-entry `Array.make` literals, exceed the
  emitted `maxRecDepth 2048`. Two errors.
- **(3d) mutable-iterator encoding.** The template's `ChunksExactMut::next` has a backward function in its result
  type, which the native `Iterator.next` field does not take (1 error), and `compact::expand_values` destructures
  `(o, iter1, next_back)` from `Zip<ChunksExact, ChunksExactMut>::next`, while the native `Zip` `next` returns a
  pair ("expected a product type, got core.iter.adapters.zip.Zip ..."; 2 errors).
- Consequential: two "Unknown constant `core.slice.iter.ChunksExactMut.Insts.CoreIterTraitsIteratorIteratorMutASlice`"
  after the failed `impl_def`.

**`compact::expand_values` does not elaborate** (errors at Funs lines 932 name clash, 933 Zip destructuring, 952
unknown `ChunksExactMut` instance). **`r0::heap::filled` elaborates**: the core scope's only error is in
`circle::secure_circle_point_from_parameter` (ok_or); no error is reported in the `r0.heap.filled` declarations
(Funs lines 2179 to 2200), and `alloc.alloc.Global` resolves to the native inductive. Because the core `Funs`
module still fails, it writes no object.

Facts about the raw text: all raw files use the module system (`module`, `public import`, `@[expose] public
section`). The templates declare their externals as `axiom`s: v 67+2, p 96+5, s 9+1, d 11, c 10+3 (Funs+Types);
compiling a template unedited adds these axioms. No raw file contains `sorry`. A compiled module writes `.olean`,
`.olean.server`, `.olean.private`, `.ir` and `.ir.sig`.

First-pass static check, kept for reference: Static library-name check (`probe-static-library-refs.tsv`, tool `host/fv_x3_libnames.py`). This is not
elaboration. It takes every `core.`/`alloc.`/`std.` path in the raw text and finds whether the native source
declares a Lean name for it. Classes:
- declared: found;
- member: a field or method of a declared structure;
- declared by the emission's own template;
- text only: the last name component occurs in the library, but only through a `«%S»` scalar template that the
  reader does not expand.

| Scope | References | Declared | Member | Own template | Text only (the `«%S»` scalar methods `to_le_bytes`, `from_le_bytes`, `wrapping_add/sub`) | Not found |
|---|---|---|---|---|---|---|
| v | 105 | 86 | 10 | 4 | 5 | 0 |
| p | 71 | 49 | 7 | 13 | 2 | 0 |
| s | 85 | 66+1 | 9 | 5 | 4 | 0 |
| d | 55 | 43 | 4 | 2 | 6 | 0 |
| c | 62 | 46 | 5 | 7 | 4 | 0 |

Every `core.`/`alloc.`/`std.` path the emission references is declared natively or by its own template; the
compile confirms there is no unknown library constant, except the cause (1) trait methods, which are structure
fields rather than declarations and so were not visible to the static reader.

**Old shim items** (`shim-items.tsv`): the three shims define 15 library items, plus four members of
`SliceIndexRangeFullSlice`, and departed from the copied text twice (`Array.from`, `Slice.from`). All are declared
natively. The compile reports no error naming any of them other than `ok_or`, whose native signature differs
from the shim's (cause 3a). Per item, "elaborates in use" means: the emission uses the item, and no error
names it; `shim-items.tsv` has the column.

## Stage C: import closure of the model theorems and port size

(Interim commit: the closure compile and the trimmed-library runs are in progress; this section is updated when
they finish.)

Root: `AspisFailureBoundModel` (both theorems are in it). Chain sources are the worktree at
27b14ab00a4e781cddd8cd8321e158b8d5c4aa94. The `lean/` directory last changed at 5bf1b2216ff, and all 80 files
of the RPL-c1 manifest have the manifest's sha256. The closure was walked down to, and not including, Mathlib,
Aeneas, Batteries, Aesop, Qq, Plausible, ProofWidgets, ImportGraph, LeanSearchClient and Lean core. Modules
resolve in this order:
1. chain sources;
2. the L187 source tree `codex-cx-replay-l187-20261109/src` (read in place);
3. the CompPoly checkout `codex-cx-replay-dry-20261026/RPz4_CompPoly` at 4165a87dd9a9ede48ee4dc5b4fe825604b8bb932,
   for the package that L187 has only as objects in `base_ref/CompPoly`. That the objects were built from this
   checkout is not verified.

Every module resolved. Tools: `host/fv_x3_closure.py`, `host/fv_x3_kinds.py`, `host/fv_x3_dependents.py`.

| Kind | Modules | Lines | Import Aeneas | Closure reaches a (d) module |
|---|---|---|---|---|
| (a) Aspis model chain | 73 | 14,342 | 0 | 42 |
| (b) CompPoly (vendored maths, Mathlib only) | 87 | 31,068 | 0 | 0 |
| (c) R1 maths / bound layer about a model | 1,253 | 156,253 | 0 | 137 |
| (d) R1 gate carrier | 38 | 8,724 | 9 | 34 |
| total | 1,451 | 210,387 | 9 | 213 |

The closure holds 73 of the 90 chain files; the other 17 are not imported by the model theorems' module.

### Kind (d), and how it was decided

The seed is a generated module (last component `Types`/`Funs`/`FunsExternal`/`TypesExternal`, or a module of
the named families) or a module that imports Aeneas. The kind then spreads, to a fixpoint, to any module that
directly imports a (d) module and whose text (comments removed) uses a name declared there. A module that only
reaches (d) transitively stays (c) and is flagged in `reaches_d`.

The column `d_tier` splits (d) by reading the content:
- generated (7): `AspisR1AdapterReconstruct.{Types,FunsExternal,Funs}`, `AspisR1PublicSerializer.{Types,Funs}`,
  `AspisR1WithdrawalValidation.{Types,Funs}`.
- aeneas-import (2):
  - `ImportUnionNamedDiscriminant`, an attribute for generated `Types`; only the generated adapter `Types` imports it.
  - `RawDigestLogCarrier`, which defines byte-log predicates over Aeneas `U8`/`Slice`.
- translated-content (13): statements over the generated definitions, for example
  `PublicSerializerFieldsRefinement431` (uses `fields`, `fields_loop`, `public_bytes`) and
  `WithdrawalValidationAmount431` (`validate_pool_v1_withdrawal_public_v1`). The chain runs through the serializer
  and withdrawal bridges (`*431`, `ExtractedPublicCheckedBridge432`), then `ExtractedAdapterStageBindingObligations`
  and `HchecksPublicComposition`, to `DecoderInstanceBoundary` (`compiled_publicParsed_of_serializer`).
- import-only (16): modules that import a (d) module but use from it only names stated over model objects.
  Examples are `R1FinalSoundness` (`hchecks_deployed_partial`, whose statement has no translated type),
  `RecordedBinaryExperimentBin`, `DecoderQueryAccounting`, the `OraclePortAdmission`/`OraclePortChecks` pair,
  `R9TwoTransactionExperiment` (`Consistent`, `Covers`), and the `R1FinalSoundnessBinPerQuery*`/`RWire*` modules.

`closure-kind-d.tsv` lists each (d) module, its importers and the names they use.

Finding: one chain module imports a (d) module directly. `AspisFailureBound` imports
`RecordedBinaryExperimentBin` (import-only tier) and uses only `RecordedBinaryExperimentBin.binaryCollision`
(five sites), defined there as `BinCombinedMerkleCollision.Coll SelectedTranscriptParams.params.iv Q run`. That
definition names no translated item, but importing it brings in `R1FinalSoundness` → `DecoderInstanceBoundary`
→ the generated serializer, adapter and withdrawal `Funs`.

Fifteen other chain modules directly import a (c) module that reaches (d). The remaining 26 of the 42 chain
modules that reach (d) do so only through other chain modules. `closure-chain-to-d-paths.tsv` gives the
shortest path for each direct entry. The main entry points are:
- the `OraclePort*` modules, reaching `OraclePortChecks`/`OraclePortAdmission`;
- `BinHonestQueryBudget` → `DecoderQueryAccounting`, reached from `AspisRowStarts`, `AspisRows40Starts` and
  `AspisRec40CallBudget`;
- `R16CanonReduction` → `R1FinalSoundnessBinPerQueryR19`, from `AspisRec40FinalLiteral`;
- `Frozen2StartChargeCompletion` → `OraclePortAdmission`, from `AspisRec40CleanRun`.

For the chain to shed (d), every path in that file has to be cut.

### CompPoly (kind b)

CompPoly is pinned to Lean v4.32.0, `fixedToolchain := true`, Mathlib 81a5d257 (v4.32.0). Its local clone
(remote `Verified-zkEVM/CompPoly`, last fetched before this task) has tags up to `v4.35.0` and toolchain commits
up to v4.35.0 (06686e4c70939af82203af21516f8ab8a21a8051, 2026-10-14). It has no ref for v4.36.0-rc2. Whether
upstream now has one is unchecked; checking needs a fetch, which the task excluded. The closure uses 87 of its
274 modules.

### Compile under the new toolchain: not run

`closure-compile.tsv` records this. No module count compiled or failed, and no error kinds exist. Prepared:
`host/fv_x3_closure_compile.sh`, one slot. It compiles in dependency order with no edits, skips a module whose
imports failed, and records exit, wall, peak RSS, error count and first error per module.

### Port size estimate (static only)

- Scope of the port: all 1,451 modules (210,387 lines). They move from Lean 4.32.0 with Mathlib v4.32.0
  (81a5d257) to Lean 4.36.0-rc2 with Mathlib 9d581dff, four minor Lean versions.
- Only 9 modules import Aeneas, and only the 22 modules of the generated, aeneas-import and translated-content
  tiers name translated definitions or Aeneas scalar or slice types. No chain module (kind a) mentions Aeneas. A port "over Aeneas
  scalar types" therefore concerns those 22 modules, which are also the ones the chain is to shed. Everything
  else is a Lean/Mathlib version port.
- Error sites: not measured. A number needs the closure compile. Until then, any figure would be a guess, and none
  is given.
- The ten modules with the most transitive dependents in the closure (`closure-dependents.tsv`), all kind (c),
  64 to 283 lines each:

  | Module | Transitive dependents |
  |---|---|
  | `AspisV8Privacy.FiniteGames` | 919 |
  | `AspisV8R17.AdaptiveOracle` | 918 |
  | `AspisV8R19.OracleResampling` | 914 |
  | `AspisV8PairedCommitment.Table` | 912 |
  | `AspisV8R19.MemoizedProgramLaw` | 911 |
  | `AspisV8R19.OracleProgramOps` | 910 |
  | `AspisV8R19.AdaptiveFirstReadLaw` | 886 |
  | `AspisV8R19.CausalFirstHitUnionBound` | 875 |
  | `FS.Statement` | 874 |
  | `FS.LemmaA` | 869 |

## Not checked

- Every compile: the library build, the 19 raw-emission modules and the 1,451 closure modules.
- Whether `~/.cache/mathlib` holds the files for Mathlib 9d581dff.
- Whether CompPoly upstream has a revision for v4.36.0-rc2.
- Whether the CompPoly objects in L187 `base_ref` were built from the checkout at 4165a87.
- Library references outside `core.`/`alloc.`/`std.`, and the `«%S»` scalar-template names, which the reader
  matched by text only.
- The (d) tiers rest on regular-expression reads of names (at least 5 characters, a short list of common names
  excluded) and on reading the modules named above; they are not an elaborated dependency analysis.

## Files

Tables in this directory:
- `closure-modules.tsv`: module, kind, d_tier, source, path, lines, sha256, aeneas_import, aeneas_mention_count,
  reaches_d, closure_imports, kind_reason.
- `closure-kind-d.tsv`
- `closure-chain-to-d-paths.tsv`
- `closure-dependents.tsv`
- `closure-compile.tsv`
- `probe-errors.tsv`
- `probe-static-library-refs.tsv`
- `shim-items.tsv`

Scripts: `../host/fv_x3_*`. Host copies are in `W/x3/bin`. Host results are in `W/x3/closure` and `W/x3/probe`,
and the extracted library source is in `W/x3/aeneas-src`. `W/x3` takes 4.7 MB.
