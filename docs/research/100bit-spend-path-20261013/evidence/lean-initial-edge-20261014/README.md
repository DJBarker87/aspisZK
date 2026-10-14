# Initial edge focused Lean evidence

This bundle collects existing capped NUC attempt evidence for 15 modules. Packaging did not rerun Lean targets. It preserves 32 attempts: 17 failed, 0 successful but superseded attempts, and 15 final successful attempts. Attempt sources are checked against receipt hashes; final source snapshots match the most recent green receipt for each module.

`source-manifest.json` records the target map, individual attempt provenance and resource receipts, final source snapshots, and `objects/initial-edge-objects.tar.gz`. The archive has one `.olean` member for each listed target under `objects/`. `runner/` captures the pinned runner and environment. The original `init-source-inventory.json` is preserved unchanged.

For `R1InitialWalk`, attempts c and d have the same source SHA-256 (`2ebee88267d556b0a19f4265d3c8c097f0af87171955495aa684c710c941fee9`) and both failed because the intended edit did not change the source between attempts. The prior bundle lacked SHA sidecars for those six attempts; sidecars here are derived from the retained snapshots and checked against the original receipts. The attempt logs, receipts, and source snapshots remain unchanged.

The old runner omitted the `R1StrictReseedDecoder-a` source snapshot. It was reconstructed from the current Lean source only after an exact receipt-hash match.

Root independently audited all 32 attempt snapshots and resource receipts,
all 15 current sources and archive members, and the 66 axiom reports from
successful builds. Every report uses only `propext`, `Classical.choice`
and/or `Quot.sound`. The nine supplementary `.source.sha256` files are
retained and verified. Redundant loose objects were removed only after
matching their archived hashes. `ROOT-VALIDATION.json` records the audit;
`SHA256SUMS` seals the bundle.

The combined `R1InitialCheckpoint-a` passed in 1.41 seconds, with peak RSS
3,529,016 KiB, zero swap and 33 axiom reports. Every target used the pinned
4G/6G/0 high/max/swap scope. Source base is
`eb1b410e87539f4840de396b98af04f50d54f184`; each attempt records its exact
source hash. The 14 central runtime fingerprints and all initializer
inventory hashes remain unchanged.

This is focused build evidence only; it makes no protocol-security or
release-closure claim. See [the bridge scope](../../INITIAL-EDGE-BRIDGE.md)
for the proved local results and remaining obligations.
