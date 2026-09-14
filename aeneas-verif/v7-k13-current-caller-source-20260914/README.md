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

This closes the complete current-source translation blocker. It is not by
itself the G1 caller-refinement theorem: the generated standard-library
externals still need their checked implementations, and the callback's exact
six-component prechallenge state must be consumed by the maintained K1.3
model. The selected SBF/CU comparison is also a separate runtime gate.
