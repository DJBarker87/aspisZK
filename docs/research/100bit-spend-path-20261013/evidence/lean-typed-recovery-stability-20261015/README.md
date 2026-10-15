# Typed recovery stability evidence

This module composes the existing C1 initialization-frame and C2 first-read table-stability theorems. The C1 and C2 first-read representations are distinct inputs, each with its own represented-trace consistency and table-replay equality. Under the corresponding existing read, consistent-full-trace, query-budget, no-collision/no-child-hit/no-root-hit, size, and table premises, it proves equality of both recovered packed-byte functions against the full trace through caller-supplied paths, then equality of the resulting total typed words. Paths remain caller supplied; this module adds no source-path geometry, transcript, parser-caller, or acceptance claim.

Final green target: `R1TypedRecoveryStability`, attempt `typed-recovery-stability-d`, exit 0, 1.84 s, peak RSS 3,516,948 KiB, zero swap; cgroup `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`. Four public theorem audits report `[propext, Classical.choice, Quot.sound]`. Attempts a and b are failed; attempt c is a superseded green with a single shared represented trace, preserved here for provenance.

Final source SHA-256: `1ae695c97a097610d6a22da8ec83f4f6c566377297e5298851d6ef74a1150754`. The focused NUC workspace was `/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013`; source and imported object pins are recorded in `source-manifest.json`.
