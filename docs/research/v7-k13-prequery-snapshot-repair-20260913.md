# V7 K1.3 pre-query snapshot repair

**Base:** `37e1f04b8790f4dc092a38e5ad08d27b00801e0b`
**Branch:** `research/v7-k13-restored-source-20260913`
**Status:** local observer repair and finite arithmetic audit checked; source
refinement and the restored actual-law proof remain open.

## Repair

The default-off `aeneas-observer` snapshot is taken before the query-batch
challenge.  At that point the disclosed final object has 256 coefficients.
The observer previously evaluated only `final256_coefficients[..4]`, which is
the later terminal width, not the pre-query width.  The repair changes only
that observer calculation to the full slice:

```rust
view.weights.dot(&view.final256_coefficients[..])
```

The selected verifier still uses its no-op observer.  This repair is a
source-correspondence correction, not a claim of an acceptance vulnerability.

## Focused Rust evidence

All Rust commands ran on `nuc.local` in fresh systemd user scopes with
`MemorySwapMax=0`, `MemoryHigh=3G`, and `MemoryMax=4G`, using
`nightly-2026-06-01`.

| Source | Command result | Evidence |
|---|---|---|
| Old source | failed as expected | The two-test regression panicked at `WeightAccumulator::dot` with `left: 4`, `right: 256`. |
| Repaired source, debug | passed | `2 passed; 0 failed`. |
| Repaired source, release | passed | systemd exit status `0`; the same focused test target completed successfully. |

The regression covers offsets 0, 3, 4, and 255, metadata preservation, and a
zero-discrepancy case.  It does not construct an accepting proof.

## Kernel-checked finite audit

`AspisFormal.K1.V7Tag73K13SnapshotLengthAudit` was compiled on the same host
with Lean 4.32.0 in a `MemoryHigh=1500M`, `MemoryMax=2G`, zero-swap scope.
The final replay exited `0`, with a 328 KiB cgroup peak.  Two elaboration
repairs made the finite spike witness use `i.val = 4` and proved its full sum
with `Finset.sum_eq_single`; no theorem statement was changed.

The explicit `#print axioms` report contains only `propext`,
`Classical.choice`, and `Quot.sound`.  In particular the failed first replay's
transient `sorryAx` report is not evidence for the corrected target.

## Regenerated source extraction

Using the pinned Charon binary
`b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c`, with
both `aeneas-observer` and `v7-production-tag73` enabled, the repaired current
snapshot source extracted successfully to LLBC:

```text
V7Tag73SnapshotFull256.llbc
SHA-256 636967d3e30da3a2a3d7668196c3942a26b848669b1a5da930aa775e3ab9f1dc
```

The focused extraction stayed below 1.1 GiB peak RSS and used zero swap.

The matching Aeneas translation is **not** accepted: it reaches the real
generic `WeightAccumulator::dot` path and fails context matching at
`crates/aspis-core/src/sumcheck.rs:1910-1913`, the `Dense` component loop.
No template external or replacement trusted helper was imported to conceal
that failure.

## Remaining gates

- `SOURCE-LINK-OPEN`: translate/refine the real full-length dot and connect the
  successful snapshot to the actual caller boundary.
- `ACTUAL-LAW-OPEN`: construct the literal candidate-directed prefix
  factorization and discharge K1.3/K1.4/K1.5 restored-stage bounds.
- The packet's other two Lean modules are retained in the worktree but are not
  claimed checked: their imports require a verified current formal cache, not
  a partial historical object graph.
