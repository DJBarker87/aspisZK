# Computable wrapper artifact audit

This separate read-only audit covers `R1ComputableTraceWitness` and `R1TraceValueDecode`. It is a follow-up artifact review only; neither target is part of the curated eight-target J1 base-descent stage list. No build or source change was made.

Both evidence bundles pass their `SHA256SUMS` checks, and the attempt snapshots, receipts, output logs, timing logs, source sidecars, object pins, and direct import pins match the bundle manifests. The local `ComputableTraceWitness.lean` source matches its green attempt digest. The local `TraceValueDecode.lean` source matches the bundle’s source digest; its bundle records one successful focused attempt, 1.57 s wall time, 3,318,116 KiB peak RSS, zero swap, 4G/6G/0 cgroup, and `[propext, Classical.choice, Quot.sound]`. Its log contains unused-simp-argument warnings but exits successfully.

`ComputableTraceWitness` preserves attempts a–c as failures and d as green (1.87 s, 3,333,972 KiB peak RSS, zero swap, 4G/6G/0). The two audited declarations report only `[propext, Classical.choice, Quot.sound]`. Its import source/object snapshots are included and pinned.

The TraceValueDecode archive’s five object members match the recorded hashes. The bundle explicitly says its `R0P.Core` object came from the pinned external cache; the included `R0P/Core.lean` is a historical source counterpart, not asserted to be the source used to build that cached object. That provenance limitation is retained here.

The module statements construct a computable witness selector agreeing with an existing projected witness under `BaseTyped`, and decode three bounded values from designated trace cells. These artifact checks do not assert spend validity, protocol/source refinement, or a security conclusion. See `review.json` for per-file pins and validation details.
