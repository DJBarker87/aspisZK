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

Kani actual destructor behavior: `trace_drop_small-scalar` passes 459 checks
(six unreachable), 146.605 s, 3,941,440 KiB, zero swap, arbitrary lengths
0..2 in all 16 columns and arbitrary stored u32 words. It checks unit return,
no panic and an unchanged separately owned output word. This bounded result
is **not** a universal write-set certificate.

The `volatile_zero_word` contract projects exactly the shipped volatile
store through M31's transparent u32 representation. Dynamic frame checking
proves the only permitted target is that word and it becomes zero; 57 checks
(two unreachable) pass, 0.540 s, 168,276 KiB, zero swap. No destructor is
stubbed. This supplies a projected P6 store certificate, composable with the
arbitrary-length heap-model theorem, but a complete actual-Drop/loop mapping
has not been supplied.

Three whole-destructor dynamic-frame experiments were stopped at the 6 GiB
MemoryHigh review, without verdicts: arbitrary small lengths (233.861 s,
6,402,728 KiB), fixed two-word columns (85.461 s, 6,384,000 KiB), and one
symbolically selected two-word column (83.215 s, 6,370,368 KiB). All swaps 0.
Each narrowed a different source shape; none was rerun unchanged or with a
larger cap. SIGTERM was sent only to that task's CBMC child; Kani reported no
successful verification. The earlier explicit-destructor call failed Rust
compilation, the renamed harness selector matched no harness, and the
32-byte output comparison failed a memcmp unwinding assertion. All remain
in the receipts. The final scalar comparison corrects that harness issue
without changing the destructor unwind bound.

## Stage 2: admission

A control-flow reference replaces the frontier loop's early return with a
carried Result and guarded while. It is added only to the existing cfg-only
reference file. Substituting it in the isolated owned constructor advances
forest translation to code generation. Two further constructor name clashes
are fixed in LLBC metadata: enum constructors and tuple struct constructors
receive distinct function names. Function bodies, IDs, calls and type layout
are not changed by those renames. Aeneas then succeeds: 5.667 s,
455,440 KiB, zero swap, 6,625 generated Lean lines. This raw output contains
unsupported externals (including Drop, records, lazy external, iterator,
array, Option/Result and slice operations) and is not admitted or compiled as
a certificate.

The full Kani validator comparison with explicit shared-root argument
checks timed out at 240 s with no verdict. Its GNU-time parent RSS is
incomplete (14,960 KiB); it is not the child peak. The replacement projects
the common pure root-helper result. Both callers pass the same immutable
tree and empty table, so this isolates control flow, not root reconstruction.
The complete semantic admission obligation remains open.

## Stage 3: Parts content

In progress.

## Stages 4–5: runtime and checker/retry

In progress. Neither join is inferred from a component theorem.

## Resource and provenance

All task jobs use MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64,
with reservation guards below the host's 55 GiB allowance and the required
linker flag. No other worker is interrupted. No wallet or key cleanup is
performed. No frozen ELF rebuild is required unless a shipped file changes.
