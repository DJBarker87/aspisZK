# R52 focused proof execution

Base `55f6f65530e6b1dbccd9c4ea23d82268974d45f9`.
Tailscale NUC: `100.108.41.90`. Initial read-only resource check reported
62 GiB total, 45 GiB available, only `init.scope` running. Existing system
swap was 7.5 GiB; all task scopes set `MemorySwapMax=0` and successful
target records report zero swaps.

Serial scopes `aspis-r52-lean-a` through `aspis-r52-lean-l` used:

```
MemoryHigh=3G MemoryMax=5G MemorySwapMax=0 TasksMax=128
```

Maximum simultaneous reservation: 5 GiB. Retained source-aware cache starts
at `/home/dombarker/project-offloads/aspis-r51-lean-20260929-i` (263 objects).
Sources: `/home/dombarker/project-offloads/aspis-r52-lean-src-20260929-a`.
Runner: `/home/dombarker/project-offloads/aspis-r21-tools-20260922-a/run_r52_lean.py`.
Every exact command, base revision, source hash, exit and resource record is
in the per-stage metadata/logs. One missing unchanged dependency (`Table`)
was compiled once in c. No cold or package-wide build was run.

## Focused failures and repairs

- a: a higher-order sum rewrite needed explicit function arguments. Fixed
  locally; b compiles the resampling leaf.
- c: explicit function-domain/observer annotations were needed in the base
  case and event corollary. Fixed locally; d compiles the program law.
- f: metavariable-driven inference through a recursively defined program
  hit the default heartbeat limit. Supplied the program and observation
  explicitly. No heartbeat increase; g compiles the finite-support bridge.
- h: the source block count needed symbolic addition arithmetic. The source
  continuation-law specialization also triggered a linter recursion limit
  through its huge finite 32-byte answer space. Replaced that specialization
  by a generic byte-program law plus the exact source-continuation evaluation
  identity. This retains the same application without expanding the finite
  state space. No recursion-limit/linter override; j compiles the bridge.
- i: a dependent launch was queued before the h result was inspected and
  retried the still-failed source leaf unchanged. It failed at that leaf and
  did not reach the next target. This scheduling error is retained, not
  counted as verification. Subsequent dependent work waited for j to pass.
- k: the stopped-program leaf passed. The small publication control then
  needed the opposite orientation of an equality already simplified by Lean.
  Fixed only that control; l compiles it and reuses the stopped leaf.

No memory-pressure kill, cap increase, large finite enumeration, new Rust
execution, SBF build or unchanged CU replay. Cosmetic linter warnings in
successful logs are retained. Existing source-control receipts are reused
only with their pinned source/artifact hashes intact.
