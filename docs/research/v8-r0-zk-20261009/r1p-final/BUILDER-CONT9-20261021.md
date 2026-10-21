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
are not changed by those renames. The structural JSON audit finds exactly
five changed scalar leaves, all in function names, the item-name index or
the function rename attribute. Exact before/after values are committed in
`builder-cont9-adaptation-audit.json`. Aeneas then succeeds: 5.667 s,
455,440 KiB, zero swap, 6,625 generated Lean lines. This raw output contains
24 unsupported externals (including Drop, records, lazy external, iterator,
array, Option/Result and slice operations) and is not admitted or compiled as
a certificate.

The full Kani validator comparison with explicit shared-root argument
checks timed out at 240 s with no verdict. Its GNU-time parent RSS is
incomplete (14,960 KiB); it is not the child peak. The replacement projects
the common pure root-helper result. Both callers pass the same immutable
tree and empty table, so this isolates control flow, not root reconstruction.
The projected-root replacement also timed out at 240.040 s without a verdict; its parent RSS is likewise incomplete. Neither failed experiment certifies the reference substitution. The complete semantic admission obligation remains open.

## Stage 3: Parts content

`BuilderInverse` proves the actual modular-exponentiation loop by induction
on the symbolic exponent, with bounds preventing u64 multiplication wrap.
`BuilderInverseResult.inverse` identifies the actual `inv_r` with `invR` for
all u32 storage words. J9343 and J9345 pass (2.31 s / 3,751,128 KiB and
1.78 s / 3,736,720 KiB, zero swaps). The failed monolithic specialization
J9342 reached kernel memory pressure at 7,169,680 KiB; it was replaced by
separate symbolic field-power and scalar-conversion lemmas, not a limit
increase. The generic loop was checked before its concrete specialization.

`BuilderPrimitiveDigests` supplies 46 identities between the actual aggregate
and component block-writer/Poseidon extractions, including all recursive
loops, round constants and full permutation. Recurrences use symbolic suffix
induction with bounds 4, 8, 11 or 16; no concrete permutation cell is
reduced. Its deterministic generator `--check` passes. J9347 passes in
4.55 s, 3,791,660 KiB, zero swap; all 46 axioms audits use only the allowed
standard axioms. This removes duplicated primitive computation as a source
of mismatch.

`BuilderDigestArguments` proves complete Result identities for the actual
note chunks, digest extraction, permutation wrapper, block/sponge/node
hashes, owner, arbitrary chunk and length selection, and chained sponge
pre-states. J9356: 2.92 s, 4,023,840 KiB, zero swap, 16 audits.
`BuilderDigestTotal` proves primitive and arbitrary-note totality for all
raw words without admission hypotheses: J9357, 1.95 s, 4,015,268 KiB,
zero swap, eight audits. The proof uses generic finite-field refinement;
no concrete hash is evaluated.

`BuilderAuxContent` derives the exact change/recipient/input digest maps,
both output occupancy records, the auxiliary callee and the full inherited
Content.aux equation from successful actual Parts. It requires neither a
transfer/withdrawal flag premise nor an assumed digest/inverse equality.
J9359: 2.03 s, 4,013,772 KiB, zero swap, eight audits. All standard axioms.
`BuilderTreeArguments` identifies the full actual membership digest loop
against `treeCurR`, including raw-word bit tests and totality (J9361, 1.96 s,
4,018,700 KiB, zero swap). `BuilderPathContent` proves all four actual path
array closures, their canonical arguments, and full Content.path from
successful Parts (J9363, 3.11 s, 4,018,648 KiB, zero swap). Six and eight
standard-axiom audits respectively. No path-array equality is assumed.

## Stages 4–5: runtime and checker/retry

In progress. Neither join is inferred from a component theorem.

## Resource and provenance

All task jobs use MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64,
with reservation guards below the host's 55 GiB allowance and the required
linker flag. No other worker is interrupted. No wallet or key cleanup is
performed. No frozen ELF rebuild is required unless a shipped file changes.
