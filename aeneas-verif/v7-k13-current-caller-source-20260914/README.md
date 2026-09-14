# V7 current prechallenge-caller translation

This receipt covers the current selected observer-capable Tag-73 caller after
two source-preserving normalizations needed by the pinned Aeneas backend:

- the log-two terminal `WeightAccumulator::dot` uses indexed, inlined helpers
  instead of retaining borrowed enum fields across loop back-edges;
- the selected shared three-dot caller uses a borrow-separated entry point and
  indexed, inlined reduction helpers instead of an array-of-borrowed-slices
  iterator.

The operation order, chunk sizes, field reductions, shorter-input `zip`
semantics, terminal relation, transcript schedule, protocol parameters, and
proof grammar are unchanged. The public array-of-slices `qm31_dot3` wrapper is
retained and delegates to the same implementation.

## Recorded run

The run on 2026-09-14 used Charon 0.1.223 and the pinned Lean-4.32 Aeneas
backend over Tailscale. Both stages ran under a 6 GiB hard memory limit with
swap disabled. The Aeneas stage took 230.586 seconds and was observed below
3.7 GiB RSS. It generated complete `Types.lean` and `Funs.lean` files; the
forbidden-term scan returned zero matches.

Hashes:

```text
LLBC  cd922292f03e24a82b58090ccc5b1e49582fd9a48d1b60ecfe75a62d0f40b7a3
Funs  72efddc9496a195f40aa8fa2c88a3fdaa355be1c3d660a107864342a684e3742
Types a93686db898c41618355a570979f1f67f20d969a17028b1a2e324fc14333a1cf
```

Current source hashes:

```text
field.rs         50f66ca87b924efe7c52a7ae274b805876d0550e16473d746d4f312e320255c3
sumcheck.rs      3f390d96a668206b9d49691cd337f58153ba70d688329697dcb73c2891dfe2dd
v6_transcript.rs 03c561a5048efc308ba4f479ebe19597a4a36dfa9b035571185372754b299fb5
```

## Kernel import

The generated graph was staged for Lean 4.32 with the same source-neutral
compatibility rewrites already audited for the earlier current-caller bundle:
fully qualified transcript namespace references, the executable mutable
iterator write-back adapter, a curried QM31 fold, and the correct `(Unit,
closure)` result for the no-op diagnostic `FnMut`.  `TypesExternal.lean` and
`FunsExternal.lean` reuse that bundle's executable Rust standard-library
models; they contain no Aspis primitive axiom.  No generated Rust function
body was replaced by a hand-written implementation.

The complete staged graph kernel-compiled on Lean 4.32.0:

```text
TypesExternal wall 1.21 s, peak RSS 2,517,768 KiB, swap 0
Types         wall 2.00 s, peak RSS 2,579,164 KiB, swap 0
FunsExternal  wall 1.73 s, peak RSS 2,565,208 KiB, swap 0
Funs          wall 23.07 s, peak RSS 3,242,632 KiB, swap 0
```

Staged source hashes:

```text
TypesExternal 26444cedd12c23c357021c819a1878743d5b368aedaba8237c0c373414bb37a1
Types         894dce5ab015727686aaf06686883eebb2c1e39aeebaa29275bb3eba87eb44dc
FunsExternal  5796fc6e5f619f9fa8d46eaf091b29831bf3ac1201f26562a1f858279ccea77b
Iterator      80cd40191de85197c50f7e7f4254ece11f6aa3571bd47aaccb9a51b73a773f67
Funs          a4001cb3700e25aee5eb04e495f0eb560d18e9c9e86ae879ca34567c9a169505
```

This closes G0: the complete current-source translation and kernel-import
blocker. It is not by itself G1. The callback's exact six-component
prechallenge state must still be derived from this caller and consumed by the
maintained K1.3 model. The selected SBF/CU comparison is also a separate
runtime gate.
