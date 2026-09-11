# Paired prefix projections to the selected raw batch

Status: GREEN, first focused attempt; source frozen. No other source was edited,
no files were staged or committed, and no package replay was run.

## Exact theorem and causal scope

[PrefixPackedQueryBatch.lean](experiments/PrefixPackedQueryBatch.lean) proves
`raw_slots_of_paired_projection`: for separately supplied C1 and C2 extracted
words, a successfully parsed **same** 621-byte query record, and both packed-leaf
projections at a fibre,

```lean
NearGammaSelectedC1.rawBatch (c1Received first) (c2Received second) gamma
  (childIndex fibre slot) = PackedQueryRecord.rawCombined gamma record slot
```

The conclusion holds for every `gamma : QM31Exact` (including zero) and every
`slot : Fin 4`. `childIndex fibre slot` is literally `4*fibre+slot`; no slot or
query reordering occurs. The C1 and C2 projection equations include the same
record's shared salt. The field equality only uses their packed values, but
retaining salt makes the premise match the authenticated-leaf interface.

The two `ExtractedWords` inputs need not coincide. In the intended consumer,
`first` is the C1-prefix completion fixed before lambda/chi and `second` is
the C2-prefix completion fixed after adaptive C2 but before OOD/gamma. The
lemma does not itself prove those cutoffs or the projection equations. It
does not create a new total word from the queried records. Unopened symbols
may be noncanonical and remain the V7 decode-or-zero totalization.

The auxiliary `batch_slots_of_paired_projection` gives the same conclusion
against the parsed `combined` value. `lanes_of_paired_projection` proves
all 29 lanes before batching; the C1 and C2 slot lemmas expose the individual
successful decoders. These are the five audited declarations.

## Reused formalization and next consumer

Only two direct imports are added: `PackedQueryRecord` and
`NearGammaSelectedC1`. The proof reuses:

- V7 `c1_received_of_exact_projection` / `c2_received_of_exact_projection`;
  `fibreIndex_initialIndex` / `fibreSlot_initialIndex`;
  `embedM31Exact_eq_algebraMap`.
- `PackedQueryRecord.c1_entry` / `c2_entry`, the canonical 621-byte record
  parser bridge, and `combined_eq_scalar_power` / `combined_eq_raw`.
- The actual selected `received29` and `NearGammaSelectedC1.rawBatch`, not
  an independently assumed batching function.

Instantiate the endpoint at each query ordinal to establish the pointwise
premise of `FixedWordQueryTerminal.OpeningEquality`, when the fixed input's
word is this same prefix-derived `rawBatch`. That closes the packed-word
algebraic seam. It does **not** close Rust's Boolean multiproof-to-typed-path
refinement, supply transcript hash-log coverage, remove explicit collision
or late-target alternatives, or prove ROM freshness. The optimized u64
decoder implementation is also not newly refined here. No sampler,
probability, polynomiality, component recovery, or global soundness claim
is attached.

Scope checks: a C1 projection alone cannot identify arbitrary helper lanes
at nonzero gamma; the C2 projection is genuinely needed. A C2 packed entry
with one noncanonical limb and another nonzero limb can differ between raw
field interpretation and decode-or-zero, so successful canonical parsing
is retained. Nothing in this theorem converts parsing success into Merkle
authentication. The degree-two helper / degree-28 claim distinction is
unchanged; this is only the literal 26 base plus H/G/D scalar-power sum.

## Frozen evidence

Research source parent: `531b50ed6cd06d5902417edf614daee137c19acb`.
Target `PrefixPackedQueryBatch`; tag `prefix-packed-query-batch-nuc-v1`.
The only run used the existing pinned NUC overlay via Tailscale
`100.108.41.90`, with the host-key alias `nuc.local` used only for key checking.
Preflight found no active build scopes/compiler and 50,094,534,656 bytes of
available RAM. The cgroup logged 8 GiB MemoryHigh, 10 GiB MemoryMax, SwapMax=0,
CPUQuota=200%; Lean 4.32.0 ran `-j1 -M9500`. Source limits remained
maxRecDepth=200 and maxHeartbeats=200000, with no local increases.

Result: exit 0; Lean wall time **2.91 s**; peak RSS **6,828,420 KiB**;
**0 swaps**; preflight and postflight `OVERLAY_PROVENANCE_PASS=1093`,
`PROVENANCE_UNCHANGED=true`. All five `#print axioms` results are exactly
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` or new axiom.
There were no failed attempts.

| Artifact | SHA-256 |
| --- | --- |
| [Source](experiments/PrefixPackedQueryBatch.lean) and [frozen source](experiments/prefix-packed-query-batch-nuc-v1-source.txt) | `c2614cc451d84b0d66f4ecb96d1676f3276138c20dacd9c7c709499dd02b1ea5` |
| [Manifest](experiments/prefix-packed-query-batch-nuc-v1-manifest.json) | `ab95bb838dfffa9980a98f64c226975015ab6a4881446d3a492ef8e94dca0973` |
| [Log](experiments/prefix-packed-query-batch-nuc-v1.log) | `c2c511e6307d2e8cc52e523aa47493c398d32530cff25a7664f56786fefaea93` |
| Remote `.olean` digest recorded in log; not copied or committed | `588c250a1bca5b864f43c7664044a9441124daae997acbdd3a081306b9d0f4ec` |
| [Inherited capped runner](experiments/run_higher_y_nuc.sh) | `5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52` |

The runner/cache research pin is `289d7356c78a4cd493fe61a54f9548f2a0c11298`,
distinct from the source parent above. Borrowed V7 pin:
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`. The frozen manifest records the
exact compiled import closure; the run did not rebuild it.
