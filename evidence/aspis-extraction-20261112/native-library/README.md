# Native Aeneas library: set-up, raw-emission probe and port size (task X3)

Status: target not yet established. This is a tool record. Nothing in it is a proof. No module named here was
compiled under the new toolchain. Stage A stopped before any download because the build host had less free disk
than the task's floor. Stages B and C therefore contain only static results, read from source text. Every
compile result asked for is marked "not run".

`W` = `~/project-offloads/future-version-20261111` on the build host. Host outputs are under `W/x3/`.

## Stage A: toolchain (stopped before download)

Free disk on the host filesystem (`df -h`, `/`, which also holds `W`): 31 GB at the start, 30 GB at the end
(1.8 TB, 99 % used). The task's floor is 60 GB, so nothing was downloaded and no toolchain was installed. The
library was not built. There is no wall time, peak RSS or disk figure for a build.

What is on the host:
- Toolchains installed under elan: v4.31.0, v4.32.0, v4.33.1. v4.36.0-rc2 is not installed.
- Mathlib checkouts found under `/home/dombarker` (depth 7): all at 81a5d257c8e410db227a6665ed08f64fea08e997
  (v4.32.0) or with no readable revision. None is at the revision the new manifest names.
- `~/.cache/mathlib`: 17,181 files, 865 MB. I did not check whether it holds the files for the new revision.
  Lake decides that, and Lake needs the toolchain.

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

Prepared but not run: `host/fv_x3_stageA.sh`. It refuses below 60 GB free. It installs the toolchain through elan
(adding it, removing nothing). It then runs `lake exe cache get` in one slot (never `lake update`) and checks
that the manifest is unchanged. Last, it runs `lake build Aeneas AeneasMeta` in one slot.

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

**Compile result per scope: not run, in all five scopes** (`probe-errors.tsv`). Prepared:
`host/fv_x3_probe.sh <scope> <namespace>`, one slot. It byte-copies the raw files. It copies each
`*External_Template.lean` to the file name its siblings import (`<ns>/FunsExternal.lean`,
`<ns>/TypesExternal.lean`), which renames the file without editing its content. Then it compiles the four
modules in order.

Facts about the raw text that bear on a zero-edit compile:
- All raw files use the module system (`module`, `public import`, `@[expose] public section`). They set
  `linter.internalConstructors`, which the old pipeline removed as unknown to Lean 4.32.0.
- The templates declare their externals as `axiom`s: v 67+2, p 96+5, s 9+1, d 11, c 10+3 (Funs+Types). Compiling
  a template unedited adds these axioms. No raw file contains `sorry`.
- The verifier `Funs` still contains the text behind the old pipeline's two name-clash rules: 5 binders
  `(compact :` with 151 `compact.<name>` references, and 6 binders or lets named `weights` with 215
  `weights.<name>` references. Whether those references resolve to the module or the local under v4.36.0-rc2 is
  unchecked. It is the cause (2) candidate for the verifier scope.

Static library-name check (`probe-static-library-refs.tsv`, tool `host/fv_x3_libnames.py`). This is not
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

No Rust-library path the emission references is missing from the native source text, so no cause (1) item is
known. Cause (3), anything else such as type mismatches or tactic and elaboration failures, cannot be seen without
a compile. Paths outside `core.`/`alloc.`/`std.` (for example `Aeneas.Std.*` helpers used without a prefix) were
not checked.

**Old shim items** (`shim-items.tsv`): the three shims define 15 library items, plus four members of
`SliceIndexRangeFullSlice`. The shims also departed from the copied text twice, because the old library lacks
`Array.from` and `Slice.from`. The native source declares every one of them, together with `Array.from` and
`Slice.from`. Elaboration of each is unchecked.

`compact::expand_values` and `r0::heap::filled`:
- `alloc.alloc.Global` is declared natively (`Std/Alloc/Alloc.lean:13`, `inductive alloc.alloc.Global | mk`).
- `core.iter.adapters.zip.Zip` is a two-field structure (`fst`, `snd`) natively (`Std/Core/Iter.lean:71`), with
  `Zip.Insts.CoreIterTraitsIteratorIteratorPair.next` and `Iterator.zip.trait_default` declared.
- `ChunksExact`/`IteratorChunksExact` are native. `ChunksExactMut` and its `next` are not native; they are axioms
  of the verifier's own templates.

Whether either function elaborates now is **unchecked**. The old error "expected a product type, got Zip" may or
may not recur against a structure; only a compile can say.

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
