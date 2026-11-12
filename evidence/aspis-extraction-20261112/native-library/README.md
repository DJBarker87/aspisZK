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

### Carrier-free object set: what was run (old toolchain, Lean 4.32.0)

The lead's design changed three times during the task; each version was run as it arrived and is kept:

| Version | Text tools | Old-toolchain result (nodes compiled / failed / skipped) | Table |
|---|---|---|---|
| plain trim, research e23c3db75f4 `ASPIS-LIB-trim_imports.py` | carrier import lines deleted | 0 / 7 / 130 of 137 | `trimmed-l187-compile-earlier.tsv` (variant `plain`) |
| frontier trim, mine, diagnostic (`host/fv_x3_trim_frontier.py`) | each deleted carrier import replaced by that carrier's carrier-free import frontier | 2 / 2 / 133 | same file (variant `frontier`) |
| mapped trim, research 6032f9ef5bd | carrier imports replaced by base modules (`IMPORT_MAP.txt`), unmapped deleted; 6 bases | 8 / 5 / 130 of 143 | same file (variant `mapped`) |
| **current: mapped + omit + drop, research 242907bd5b0** (`README-ORDER.md`) | map; 16 `OMIT_MODULES.txt` deleted from import lines; `drop_decls.py` removes 16 declarations in 10 modules; chain from future-version d01246c1052 appended | **47 / 13 / 144 of 204** (127 nodes + 77 chain) | `trimmed-l187-compile.tsv`, `trimmed-l187-error-kinds.tsv` |

Current run: `host/fv_x3_pipeline3.sh` (text steps), then `X3-C-map3-old` (one slot, exit 0, wall 5:26.76, peak RSS
6,170,828 kB, scope peak 2,472,927,232 B, no memory events). LEAN_PATH: `W/x3/map3-old/out` first, then the L187
`objs` and `base_ref` by reference. All 18 aspis-lib files and their sha256 are in `W/x3/aspis-lib3/SHA256SUMS.host`
(for example `trim_imports.py` 2d4078b2304ba762928ee5c89687c0a6c2d502986128a14645a58f1b45756d1d, `drop_decls.py`
c92d0e75c149be3f73ea4b6086455470db9f77c72d1ef945f50e4f3afd941aaa, `DROP_DECLS.tsv`
45b096d7fef46260e07b20043919cf3c4dbc2b5a386c69f36e2cca6dea6c6efc, `OMIT_MODULES.txt`
fdea48ec0a29b70c174b35044ce83280c7ab78ea36e4b71afe199e0664c43d3a). Records copied here: `trim-record.tsv` (26 modules),
`drop-record.tsv` (16 declarations, all found once), `drop-decls.tsv` (unchanged; no addition was made, see below). Chain
sources: the 77 files of d01246c1052; `AspisFailureBound` and `AspisRowStarts` hash as in `repoint/diff-vs-before.tsv`.

**Graph check before compiling** (`trimmed-graph-check.tsv`, kind (d) plus the 16 omitted modules counted as excluded):
121 of 127 nodes and 55 of 77 chain modules are clean. Not clean:
- the base modules `AspisLib_Guard` and `AspisLib_Tag` import `R19BudgetOriginalReads`, which is in `OMIT_MODULES.txt`.
  The pipeline trims only L187 modules, so the bases keep that import; four nodes downstream of `AspisLib_Guard`
  inherit it (`OraclePortCompletionDraft`, `OraclePortStoredAcceptanceC6`, `OraclePortStoredReductionC7`,
  `OraclePortFrozen2C6`);
- the chain module `AspisOneTxDecision` imports `OraclePortFrozenOrderDecision`, also in `OMIT_MODULES.txt`, and
  `AspisLib_Guard`; 22 chain modules, including `AspisFailureBound` and `AspisFailureBoundModel`, reach an omitted
  module through it. Chain sources were not edited.

**Coherence hazard.** An omitted module is not compiled, so an import of it resolves to its L187 object, whose own
imports (for `R19BudgetOriginalReads`: `BinHonestStartFrames` and below) now resolve to the trimmed objects that
shadow the originals. Lean 4.32.0 loads such a mix without a check. `AspisLib_Tag` compiled this way (exit 0); that
result is not evidence of anything and is marked here as incoherent.

**Failures (13), first error each** (`trimmed-l187-compile.tsv`):
- 11 fail at an `open` line with "unknown namespace" (`FS`, `FS2.Duplex`, `AspisV8R19.DuplexFrames`,
  `AspisCircleGroupOrder`, `R15WriterModel`): `R16CanonReduction`, `OraclePortDataChoiceDraft`,
  `OraclePortSelectedArithmeticC4`, `R9PoolCheckpointCodec`, `OraclePortStoredProbabilityC7`,
  `OraclePortFrozenOrderRecoveryStep`, `OraclePortFrozenOrderLeaves`, `OraclePortFrozenOrderAccepted`,
  `OraclePortFrozen2Trace`, `Frozen2StartChargePrefix`, `R16DecisionCheckpoint`. The deleted import line (an
  omitted module or an unmapped carrier) was also the module's only route to namespaces it opens; the earlier
  frontier variant shows that replacing the line by the carrier-free frontier of the deleted module keeps them.
  This is a consequence of deleting import lines, not a use of carrier content.
- `BinHonestQueryBudget`: "Unknown constant `recorded_starts`" at line 119, the `#print axioms recorded_starts`
  that `drop_decls.py` leaves behind (its span stops at a line starting with `#`). Every dropped declaration whose
  module prints its axioms will fail the same way.
- `OracleDecisionFeasibilityBudget`: "Unknown identifier `R19BudgetOriginalReads.verifier_queries`" in theorem
  `queries` (line 66): a declaration of an omitted module is used. The module is not in `top_closure_modules.tsv`.

**Needed modules that fail** (in `uses/top_closure_modules.tsv`, needed-constant count): `R16CanonReduction` 11,
`OraclePortFrozenOrderRecoveryStep` 9, `Frozen2StartChargePrefix` 5, `OraclePortSelectedArithmeticC4` 4,
`OraclePortDataChoiceDraft` 1, `OraclePortFrozenOrderLeaves` 1, `BinHonestQueryBudget` 1. In the first six every
declaration after the failed `open` fails, the needed ones included. Under the lead's rule this stops the run: no
declaration was added to `DROP_DECLS.tsv` (the one candidate, `OracleDecisionFeasibilityBudget.queries`, is noted
above), and nothing was patched.

**The 26 modules of `kindc_declarations_to_drop.tsv` against the prediction.** 16 are in `OMIT_MODULES.txt` and were
not compiled, as predicted. Of the 10 with dropped declarations: `BinHonestQueryBudget` fails (leftover `#print`),
`R16CanonReduction` and `OraclePortDataChoiceDraft` fail (unknown namespace), the other seven are skipped because an
import failed; none of the 10 compiled, so the prediction that the drop is sufficient is untested for them.
**Leaving out un-needed modules.** All 16 omitted modules are imported, directly or transitively, by needed
modules, so they cannot be left out by import closure alone; the trim deletes those import lines instead. Over the
trimmed graph (kind (d) excluded, the bases standing in for the five kind (d) modules in the needed list), the
needed set with its imports is 1,410 modules (73 chain, 87 CompPoly, 1,244 kind (c), 6 bases; 200,537 lines). The
closure modules outside it are the 38 kind (d) and 9 kind (c) modules (1,126 lines).

**Chain under the old toolchain:** 37 of 77 compiled; 40 skipped behind failed imports;
`AspisFailureBoundModel` is skipped (`AspisFailureBoundJoined` not compiled). **The five checks were not run**:
they need the `AspisFailureBoundModel` object.

### Pass 2 under the new toolchain (partial)

Pass 2 was run on the set of the mapped version (6032f9ef5bd): CompPoly (87), the 1,116 kind (c) modules whose
closure never reached (d), and the 8 compiled nodes, 1,211 modules and 174,218 lines, in one slot, resumable
(`host/fv_x3_closure_compile.sh` keys each success by source sha256 and import list). It was paused at module 634
to give the trimmed runs the slot, as their priority required. The untouched kind (c) modules and CompPoly are the
same in the current version, so these rows carry over. Result over 634 processed modules
(`closure-compile-pass2.tsv`, `closure-compile-pass2-error-kinds.tsv`): **227 compile unchanged, 10 fail, 397
skipped** because an import failed. Failures, first error kind each:

| Error kind | Sites | Modules | Example |
|---|---|---|---|
| changed simp behaviour (unsolved goals after `simp`) | 4 | 1 | `FS2.DuplexTrace:175` |
| rewrite / unfold equation lemmas | 3 | 3 | `R1PublicInitFrame:57` "Failed to rewrite using equation theorems for `absorbA`"; `R1PrefixedStateCodec`, `R1D18PointWeights` |
| resource (kernel deep recursion) | 3 | 3 | `AspisFormal.CircleFibreRoots:78`; `AspisV8R15.ExactTowerChord`, `R1UnifiedLabels` |
| kernel "excessive memory consumption" and other | 3 | 3 | `AspisV8R15.ExactTowerFinite:21`; `R0P.SemBadSets`, `R1AppendCopyLinks` |
| type class / elaboration | 2 | 1 | `AspisFormal.CircleFibreRoots:94` "failed to synthesize NoZeroDivisors (ZMod P)" |
| tactic behaviour (`rfl`) | 1 | 1 | `R0P.SemBadSets:1170` |

No error names an Aeneas scalar API (none of these modules uses Aeneas) and no renamed Mathlib lemma appears among
first errors so far. The skip count is large because `FS2.DuplexTrace` sits under most of the closure (`FS2.*` has
more than 860 transitive dependents), so most of pass 2 is not yet measured: the port size in error sites cannot
be given until those ten modules compile. Pass 1 over the untrimmed closure was not run (not needed, per the lead).

### Port size (current state of knowledge)

- Set to carry: 1,410 modules, 200,537 lines (needed set over the trimmed graph, above).
- Measured under Lean 4.36.0-rc2 so far: 634 modules processed, 227 compile unchanged, 10 fail with 16 error
  sites; everything else is unmeasured behind those 10. The ten modules everything else depends on most are all
  kind (c) (`closure-dependents.tsv`): `AspisV8Privacy.FiniteGames`, `AspisV8R17.AdaptiveOracle`,
  `AspisV8R19.{OracleResampling, MemoizedProgramLaw, OracleProgramOps, AdaptiveFirstReadLaw,
  CausalFirstHitUnionBound}`, `AspisV8PairedCommitment.Table`, `FS.Statement`, `FS.LemmaA`; all ten compile
  unchanged under Lean 4.36.0-rc2.
- CompPoly v4.35.0 under the new toolchain (diagnostic): prepared (`W/x3/comppoly-v4.35.0`, 393 modules, 123,740
  lines, commit 06686e4c70939af82203af21516f8ab8a21a8051), not run.

## Not checked

- The five chain checks (a to e): `AspisFailureBoundModel` did not compile.
- Pass 2 beyond module 634 of its set, and pass 2 over the chain and the bases.
- CompPoly v4.35.0 under the new toolchain.
- Whether CompPoly upstream has a revision for v4.36.0-rc2 (needs a fetch).
- Whether the CompPoly objects in L187 `base_ref` were built from the checkout at 4165a87.

## Files

Tables in this directory:
- `closure-modules.tsv`: module, kind, d_tier, source, path, lines, sha256, aeneas_import, aeneas_mention_count,
  reaches_d, closure_imports, kind_reason.
- `closure-kind-d.tsv`
- `closure-chain-to-d-paths.tsv`
- `closure-dependents.tsv`
- `closure-compile-pass2.tsv`, `closure-compile-pass2-error-kinds.tsv`
- `trim-record.tsv`, `drop-record.tsv`, `drop-decls.tsv`, `trimmed-l187-compile.tsv`, `trimmed-l187-error-kinds.tsv`,
  `trimmed-graph-check.tsv`; earlier versions in `trim-record-earlier.tsv`, `trimmed-l187-compile-earlier.tsv`
- `probe-errors.tsv`
- `probe-static-library-refs.tsv`
- `shim-items.tsv`

Scripts: `../host/fv_x3_*`. Host copies are in `W/x3/bin`. Host results are in `W/x3/closure` and `W/x3/probe`,
and the extracted library source is in `W/x3/aeneas-src`. `W/x3` takes 4.7 MB.
