# ResourceAvailable v1 — OFFLINE operator-policy proposal

Pure `ResourceAvailable_go.evaluate(old,before,after,Q,phase=...,expected=...)`
uses the new global MemAvailable reserve policy in CRITERIA.md. It has no live
provenance. `read_only_admission` always raises; no CLI consumer is installed.
The copied full scanner is observer preparation only; this job never called it
against a real host. Do not treat `allowed` as operational launch authority.

Nonmutating, network/host-read-disabled offline entrypoint (small summary default):

    python3 -B tools/resource-available-20261024/ResourceAvailable_audit.py

`--details` explicitly emits bounded diagnostics and the complete sealed input
manifest, never the complete 15,015-event stream. The receipt wrapper records
exact command, revision, source/dependency/interpreter hashes, exit, wall, RSS,
swap and N/A axioms. Completed `audit-final` is the authoritative result; reuse
it rather than rerunning unchanged. An original stream/report over 5 MB is only
represented by hash+size. Existing meaningful event shards remain immutable.

The before/after API domain change is deliberate: raw counters remain uint64;
unused signed exclusive/current/stat/subset/type/LRU correlations are retained
only as diagnostics. Frontier B is independent and scope binding calls only the
new observer. Existing visibility, hierarchy, PID, controller and control checks
still gate evaluation. Causal replay matches full original raw snapshots.

All results are historical counterfactuals. Next work needs separately authorized
fresh prospective observation, real independently capped GO and consumer checks.
No host, scope, consumer, build, extraction, Rust, Lean, Kani, ELF or adoption work
was performed. Final Kani remains 59/60; security target not yet established.
