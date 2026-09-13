# V7 failure-side restoration and source-isolated observer

**Base:** `5c5da9951c3d0a2bfd419cb95c257441eced4aaa`  
**Scope:** additive September 13 packet; no protocol or security-parameter change.

## Integrated source and proposed formal leaves

The packet installer accepted the local full-width predecessor without drift.
It added the following proposed, uncompiled maintained leaves:

- `V7Tag73FiniteSubkernel`
- `V7Tag73AdaptiveFreshAccounting`
- `V7Tag73RestorationRetryAccounting`
- `V7Tag73PrequeryWeights256`
- `V7Tag73StoredQueryBatchChild`
- `V7Tag73QueryBatchChildFailure`

It also adds the focused observer test.  These are retained as proposed proof
bodies; they are not evidence that the same-law restored K1.3/K1.4/K1.5
inequalities have been discharged.

The observer-only preparer was reviewed before application.  It changes the
already repaired full-width snapshot only from the generic terminal-dot call
to the default-off `prequery_dot_256` helper, and appends that helper.  It
does not change `sumcheck.rs`, a production caller, feature selection, the
terminal algorithm, or any security parameter.  The helper performs the 256
fixed-array iterations and calls the real `WeightAccumulator::weight_at` for
each index.

## Focused Rust evidence

On `nuc.local`, with `nightly-2026-06-01`, one cargo job, and a systemd
scope with `MemoryHigh=3G`, `MemoryMax=4G`, and `MemorySwapMax=0`:

```text
cargo test -p aspis-core --features aeneas-observer \
  --test v7_prequery_observer_next
```

passed **7/7**.  The corresponding `--release` target also exited `0` under
the same cap.  The tests cover all 256 positions, dense and structured
covectors, deferred masks, copied metadata, and the unchanged four-entry
terminal operation.  They do not prove an accepting production proof.

## Source extraction

The patched snapshot extraction succeeded with the pinned Charon binary:

```text
V7K13Observer256R1.llbc
SHA-256 40cecac21ddb6530494ee7e21ad4ac37ce09dcccfb4ebce923a2a870857cbd3c
```

The reachable observer no longer calls `WeightAccumulator::dot`.  Aeneas
instead reaches the real `WeightAccumulator::weight_at`, where the current
toolchain fails its context matcher at `crates/aspis-core/src/sumcheck.rs`
lines 802--809.  The failure is in the `Multilinear` component iterator/borrow
path, not in the full-width observer loop or terminal-dot Dense loop.

An isolated `weight_at` extraction was also regenerated with the historical
`-loops-no-rec` shape.  The produced generated files contain only partial
dependencies and template externals; no generated template was imported, and
no hand-written Lean substitute or project axiom was added.  Therefore this
does **not** establish the helper's source-reflection theorem.

## Honest status

| Gate | Status |
|---|---|
| Full-width source-isolated Rust helper | focused tests passed |
| Snapshot LLBC extraction | complete |
| Helper/`weight_at` Aeneas source bridge | SOURCE-LINK-OPEN |
| Six packet Lean leaves | PROPOSED-UNCOMPILED |
| Actual restored K1.3/K1.4/K1.5 probability bounds | ACTUAL-LAW-OPEN |

The next required source repair is a semantics-preserving, Aeneas-compatible
normalization of the real `WeightAccumulator::weight_at` iterator/borrow path,
followed by a generated-source proof of the 256-term loop.  It must not be
replaced by an opaque callback or used to revive the rejected direct-ROM
prefix-independence route.
