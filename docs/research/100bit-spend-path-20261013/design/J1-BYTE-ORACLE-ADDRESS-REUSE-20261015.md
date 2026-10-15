# Byte-address oracle reuse inventory

Read-only interface inventory at worktree revision `3c79ec30fa44f408c716bb345050c137e907fa67`. This corrects an earlier overstatement: `Addr.toBytes` is **not injective on all padded addresses**. No theorem or security conclusion is asserted here.

## Bounded address representation

In `docs/research/v8-fs-generic-20261006/lean/FS2/Duplex.lean` (`Addr` lines 34–52),

```lean
abbrev Addr (L : Nat) := List.Vector (Option Byte) L
def toBytes (a : Addr L) : Bytes := a.toList.filterMap id
```

Thus `toBytes` drops `none` wherever it occurs, not only in trailing padding. For `L ≥ 2`, `[some b, none, …]` and `[none, some b, …]` are distinct addresses with the same byte list. `Addr.ofBytes_injective` (lines 48–52) proves injectivity of `Bytes → Addr L` under length bounds; it does not prove injectivity of `toBytes : Addr L → Bytes`.

The current canonicalization module, `lean/CanonicalByteAddress.lean` (SHA-256 `de19a4132c9e98b8c1a3b67a984c8055da34d672aa6fd9ff3ebe47ffd948967c`), defines `normalize a := Addr.ofBytes a.toBytes (length_le a)` and `Canonical a := normalize a = a`. It proves `toBytes_normalize`, `normalize_ofBytes`, `normalize_idem`, and `canonical_ofBytes`; it does not export a `toBytes_injective` or `canonical_toBytes_injective` theorem. Injectivity restricted to `{a : Addr L // Canonical a}` follows from the definitions: equal byte projections give equal normalized `ofBytes` addresses, and canonicality identifies each normalized address with its input. That restricted fact is a small missing lemma, not a property of all `Addr L`.

`UnifiedSampler` constructs addresses through bounded frame helpers returning `Addr.ofBytes`; the initial, absorb, squeeze, and advance asks are canonical by `CanonicalByteAddress.canonical_ofBytes`. The sampler type nevertheless remains `Sampler (Addr L) …`.

## Program mapping and oracle laws

`docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/OracleProgramOps.lean` (SHA-256 `dd47c1cb0e8a9a4df4966987f0c413f7b66db20de122e2d46b293833d523ab4d`) provides:

- `rename (label : I → J) : Program I A O → Program J A O`;
- `eval_rename`, mapping the trace through `label` and evaluating the old program under `H ∘ label`;
- `lazy_rename`, transporting memoized/lazy laws across an **injective** label and pulling a target table back by composition. It requires finite answers and decidable equality on both address types.

`FS2.Sampler.toProgram` in `docs/research/v8-fs-generic-20261006/lean/FS2/Statement.lean` is generic in its address type `I`, so a sampler already expressed over `Addr L` can be converted to a `Program` and renamed. No sampler-specific address-map theorem was found. `eval_rename` itself needs no injectivity, but `lazy_rename` does. Therefore using `Addr.toBytes` for randomized/cached-law transport needs proof that asks are canonical and a subtype-restricted program (or another injective restricted map). The unrestricted padded address domain cannot use `lazy_rename` with `toBytes` as its injection.

`OracleFiniteSupport.lean` (SHA-256 `b1d422366616d7193fa919fb03963a13c0d84d1d55f43d807d554e01aa1e0237`) and `CachedFiniteSupport.lean` (SHA-256 `86f05e3e15ab72db8a23490848bc826e66e145010f9b2420a048bbcc97bb3856`) provide arbitrary-address finite-support laws: `support`, `restrict`, `extend`, `finite_support_oracle_law`, `cached_law`, and `own_support_law` are polymorphic in `I`, requiring finite answers and decidable address equality, not a finite address type. They randomize the finite set of addresses reachable across all branches and can retain an arbitrary existing table. `QueryObservedProgram.cached_oracle_law` already instantiates this with `I := Bytes` for the older q22 program.

`MemoizedProgramLaw.eval` and `Program` are generic in `I`. Its complete-table laws `exact_oracle_law`, `empty_oracle_law`, and `outcome_event_law` require `[Fintype I]`, so they cannot directly provide a uniform random table over all `Bytes`; finite-support/cached laws avoid that requirement.

## Current R1 and FS2 boundary

`SelectedTranscriptParams.lean` (SHA-256 `489f8b49c6a102f85c511ad4f4907dbeca479322b7184a563eda8c4a17c2dce0`) fixes `L = 131072` and message maximum `D = 3717`. `DuplexSamplers.lean` (SHA-256 `6ae5ba2277f2881deb909fa60667dab008be0a02b2d55f9ec5c20f698fa5e4a3`) defines `plain`, `initial`, and `reseeded` over `Addr L`; its eval and independent-answer-law lemmas are reusable at that bounded type. `UnifiedSampler.lean` uses them for its 33 rows, while `LiteralTranscript.lean` (SHA-256 `2b76b95f5dffb2856f1af3884859d3d8d16e60bf47c0950559fe3c5e44ec4ed6`) retains the same bounded sampler type.

FS2 `ChainLemma` and `LemmaA` in `FS2/Statement.lean` and `FS2/LemmaA.lean` quantify over arbitrary `I`, with `[DecidableEq I]`, finite/nonempty answers, and sampler/decoder density premises, but no `[Fintype I]`. In contrast, the concrete duplex collision-counting section in `FS2/Duplex.lean` and no-collision results in `FS2/DuplexTrace.lean` use `Addr L`; collision density counts candidate addresses in the finite address space. Those bounded collision-budget results do not become all-`Bytes` results by renaming alone.

Existing byte-indexed execution models include `SamplerObservedProgram.oracle_program`, `QueryObservedProgram.oracle_program`/`cached_oracle_law`, and `R137TranscriptPrimitiveBridge`. They use `H : Bytes → State`, but cover older sampler/transcript primitives, not the current 33-row R1 decoder and collision accounting.

The reusable interfaces cover interpreting a finite program against a `Bytes` oracle, mapping its asks, finite-support oracle laws without finite address space, and generic FS2 first-read bounds. Missing R1 interfaces are a Bytes-indexed current protocol/decoder and corresponding address/collision accounting. A byte-indexed adversary program may include queries outside the canonical bounded sampler image; those remain distinct raw byte strings, but the sampler alone does not model their control flow or charge them. This note leaves the scope choice to the root.

## Source pins

The listed SHAs are working-tree file hashes at inventory time; the worktree revision was `3c79ec30fa44f408c716bb345050c137e907fa67`. No source files were changed and no Lean build was run for this inventory.

## Focused program-label components checked

Three focused Lean targets are now preserved in [the byte-oracle program-reuse bundle](../evidence/lean-byte-oracle-program-reuse-20261015/README.md): `R1GenericProgramRenameMass.independentMean_rename` proves equality of independent-answer means after renaming program labels and mapping the observation; `R1CanonicalAddressEmbedding.toBytes_injective` proves injectivity only for the subtype of canonical padded addresses, and `image_length_le` bounds their encoded byte length; `R1ProgramLabelRestriction.rename_restrict` proves that restricting a program under an `AllLabels` premise and then renaming by subtype projection recovers the original program.

These checked components fill the representation and independent-mean plumbing recorded above. They do not establish `AllLabels` for every continuation of the current R1 adversary, do not show that the full adversarial program is the restricted bounded sampler, and do not transfer a shared-oracle law using a noninjective label map. The restriction theorem's all-continuations premise remains explicit at each use.

Two more focused targets are preserved in [the program-sampler map bundle](../evidence/lean-program-sampler-map-20261015/README.md). `R1ProgramSamplerMap.toProgram_fromProgram` gives a sequential done/ask sampler view of a program, and `independentMean_map` transports output-only independent-answer means through address renaming. `R1LiteralByteSampler.eval_eq` identifies the renamed literal sampler's evaluation trace and output with the original evaluation under `H ∘ Addr.toBytes`; `independentMean_eq` gives the corresponding output-only independent-answer mass equality for all-byte addresses. These are execution and independent-answer facts. They do not prove an overlength fallback, a decoder, first-read injection, an adversarial shared-oracle bound, or source refinement; the mapped sampler construction does not by itself transfer `follow` or `INJ`.

That sampler premise is now proved separately by `R1UnifiedCanonicalLabels.samp_allLabels`, preserved in [the Unified sampler canonical-label bundle](../evidence/lean-unified-canonical-labels-20261015/README.md). Its quantifiers cover every row index, prefix, message, and continuation of the 33-row sampler, including the invalid-message totalization branches. This supplies `AllLabels CanonicalByteAddress.Canonical` for the sampler program, so the checked restriction theorem applies to that sampler. The result still says nothing about extra queries in an adversary's larger program or a decoder that combines the sampler with adversarial logic; those need their own all-label premise and oracle-law argument.
