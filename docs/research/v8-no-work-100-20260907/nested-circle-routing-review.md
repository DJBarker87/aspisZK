# Nested secure-circle routing prerequisites

`experiments/NestedCircleRouting.lean` is checked, NUC v3, exit 0, ten
standard-only axiom audits. It proves concrete decoder/classifier and
consumed-tail prerequisites. **It does not prove full nested-source routing,
finite-tape coupling, or sampler mass.**

## Checked interfaces

The detailed `limbStatus`, `limbsStatus`, and `ordinaryStatus` distinguish
short input, exhausted limb fuel, a final layout-guard failure, and success.
Their `forget` projections equal the existing literal V7 limb/four-limb/
ordinary prefix decoders, including failure. A hard limb failure remains a
hard failure after appending input. No `none` is silently treated as a field
value or assumed to mean an exhausted retry cap.

`ordinary_source_tail` derives the actual block cut and bounds from a
successful **source decoder** run. `ordinary_cursor_tail` then derives

```text
decoded.remainingBlocks = tape.drop (cursor + decoded.blocksUsed)
0 < decoded.blocksUsed ≤ 4
cursor < cursor + decoded.blocksUsed ≤ tape.length
```

No expected suffix, fixed-four-block alignment, or honest result is supplied.
The final record returned by a nested circle/distinct decoder retains only
the **last ordinary call's** `blocksUsed`/`wordsUsed`; cumulative consumption
must be obtained through successive tail cuts.

The new block-controller definitions retain three first-circle attempts and
three distinct-second attempts, each with three circle attempts. They choose
`preferredSlot` from the prior state, without an answer argument. The checked
controller lemmas immediately abort on classified hard failure in either
phase and leave success/abort results unchanged under later ghost padding.
The separate layout/short-input-at-four branches remain explicit; their
unreachability on suitably sized valid source prefixes is not assumed or
proved here.

Its slot type has cardinal `3*4 + 3*3*4 = 48`. These are squeeze-output slots;
paired duplex-advance coordinates are separate, up to another 48. Neither
this cardinality nor the controller definitions identify chronological input
with fixed disjoint four-block windows.

## Reuse and remaining coupling

The only direct import is the previously checked `DistinctCircleDecoder`,
which brings the pinned V7 prefix decoder/control interfaces. The controller
matches their intended branching, but its **whole accepted-run refinement**
has not yet been checked. In particular, it must be proved that each accepted
ordinary prefix consumes every whole block in `pending`, so `afterOrdinary`
does not discard a whole unread block.

The relevant truncation/locality mathematics already exists at borrowed pin
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`:

- `V7Tag73VariablePrefixGammaSampler.decodeOrdinaryPrefix_take_blocksUsed`
  (line 188; source SHA `5395e710e188f1f7e2085fbf84304fd040215446be7349d75061a540e22dea1f`).
- `V7Tag73VariablePrefixGammaFlatRouting.decodeOrdinaryPrefix_of_matching_consumed_prefix`
  (line 658; source SHA `f99a9cd8160535f3bab41c6bb87bc775ff7d39cabe431b00aed1a0981f214041`).

These have matching block-discard conventions, but their full import closures
meet incompatible native/overlay cache variants. A narrow permitted source
port/import and the new controller composition are needed, not a new proof
of the already established generic truncation fact.

The useful subsequent theorem is: the actual first-circle3 run followed by
distinct3(circle3) on its returned suffix agrees with the controller on the
same finite chronological tape; visited destinations are unique and selected
before their answers. Then V7's `PreAnswerSlotMachine.fullCoordinateEquiv`
can supply a lossless named-slot/residual decomposition, with unvisited
slots filled **after halt**. The literal source lookup/advance alignment must
also be proved. Alternatively, stopped-prefix tail uniformity can supply the
history-uniform one-step law for `BoundedRetryKernel`. Neither route permits
an update to inspect unused padded blocks or infers fresh SHA inputs from
transcript labels. No bounded-retry probability law follows from this leaf.

## Focused build evidence

Working parent: `15700387af1d52af4b7ddff8de92541ec2891ff2`.
Inherited scope parent: `289d7356c78a4cd493fe61a54f9548f2a0c11298`.
Borrowed sources remain pinned at `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
No old source, production Rust, cache boundary, or protocol default was edited.

| Attempt | Exit | Wall seconds | Peak RSS KiB | Notes |
| --- | ---: | ---: | ---: | --- |
| v1 | 1 | 3.38 | 6658852 | Local draft syntax, Option-bind reduction, and layout-guard glue errors; no resource failure. |
| v2 | 1 | 3.39 | 6658732 | Nine audits standard-only; only ordinary classifier projection failed due to splitting the `forget` match before the layout condition. |
| v3 | 0 | 3.64 | 6692524 | Explicit status/layout split closed the projection; all ten audits use only standard axioms. |

All swaps were zero. Every version's `.log`, `-source.txt`, and
`-manifest.json` is retained under `experiments/nested-circle-routing-nuc-vN`.
Failed logs' temporary `sorryAx` entries are not release evidence; none remain
in v3. The source equals its v3 snapshot byte-for-byte.

Execution used Tailscale numeric IP `100.108.41.90` and the inherited
`run_higher_y_nuc.sh` with target `NestedCircleRouting` and fresh version tags.
The log records the exact Lean 4.32.0 command, `-j1 -M9500`, MemoryHigh 8 GiB,
MemoryMax 10 GiB, MemorySwapMax 0, and CPU quota 200%. The initial preflight
reported no other user build scope and 43 GiB available. Builds were
serialized; the slot was handed back between v2 and v3. Final provenance:
871 entries passed and remained unchanged. Native package artifacts are a
pinned-revision cache boundary, not a package compilation replay.

Final SHA-256:

- Source/snapshot: `632a8bdd960b67d62c97b1b49926f5113a910aaf74d6bbe21976efb19c2c2836`.
- Olean: `61bd96ba4e2c30c90bbca4e632b0ef0e730ca27f86ef4630150817340305ec38`.
- Log: `074dc874e0e9c00690c87c856d33aa3aff5307354c93a3d1be4cdce58eebacc9`.
- Manifest: `8b333315f2dcd4a9aac362f4cb064a03340c4d5deb35bb6fcea87b14cc1a0c80`.
- Runner: `5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.

Reused direct/prefix source hashes:
DistinctCircleDecoder `092d83bd281d5e3c6299b50a744c0875976386abea962bc093e7459a3df886f6`;
V7Tag73SamplerDecoder `e5bdf7fb6513decec05bdeb54789f1ab35541c2389aab2f9ec0339f2dc14aa14`;
V7Tag73IncrementalSamplerControl `d9ba0ee0fbbc4e22b84b84bc117b3521104b4cf56b9a969d7a0d87605ec6c6a6`.
The borrowed files were checked unchanged against their pin with read-only
`git diff --exit-code`.
