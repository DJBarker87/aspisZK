# Builder continuation 9

Branch `codex/cx-builder-ref9-20261021`, base `a2b628d7d`.

## Scope

Continue the D103 destructor boundary, semantic admission, Parts content,
source runtime and fixed-event checker/retry joins. No existing privacy or
quotient module is edited. No production Rust is edited.

## Stage 1: zeroization observation boundary

The exact Charon flag is:

```
--opaque 'crate::state_only_trace::{impl core::ops::drop::Drop for crate::state_only_trace::StateOnlyTraceFoundation}::drop'
```

The resulting LLBC contains exactly one matching `drop`, marked Opaque with
body `"Opaque"`; its implementation is neither deleted nor changed. The
initial audit incorrectly expected JSON null for an opaque body. Fixing that
audit allowed the already generated LLBC to continue; Charon was not rerun.
The proposed alternate-name extraction was cancelled during reservation
waiting and generated no extraction receipt.

The footprint includes all owned Vec buffers. It cannot mean only the inline
`[Vec<M31>;16]` headers. `BuilderDropObservation` proves a sequential heap
specification for arbitrary footprints and byte values: writes stay within
the listed footprint; the result is `ok ()`; observations at disjoint retained
addresses are preserved. J9338: exit 0, 1.26 s, peak 2,533,612 KiB, swaps 0;
five audits use only propext, Classical.choice and Quot.sound. This is a
kernel-checked heap-model rule. Its `P6Route` explicitly requires source
correspondence; it does not claim Kani soundness as a Lean axiom or supply an
unverified source certificate.

Forest extraction now advances beyond `&raw mut` and fails at the frontier
validator: `incremental_merkle.rs:308–343`, `Unexpected return`,
`InterpLoops.ml:169`. Charon: exit 0, 11.444 s, 616,396 KiB, swaps 0.
Aeneas: exit 2, 3.135 s, 458,096 KiB, swaps 0. This remains an exploratory
reference-source extraction with the inherited P6 substitutions/opaque
records and external layer, and the metadata-only PairLeaf constructor
rename. No successful aggregate source certificate is claimed.

## Stage 2: admission

In progress. The next isolated target is the frontier-validator early return.

## Stage 3: Parts content

In progress.

## Stages 4–5: runtime and checker/retry

In progress. Neither join is inferred from a component theorem.

## Resource and provenance

All task jobs use MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64,
with reservation guards below the host's 55 GiB allowance and the required
linker flag. No other worker is interrupted. No wallet or key cleanup is
performed. No frozen ELF rebuild is required unless a shipped file changes.
