# Lead-only quiet timing plan

Do not execute until the lead agrees a quiet window with Stream A and the
three ELF pins, pinned fixture comparisons, and 1,000-pair differential gate pass.
Candidate Rust source: `6be26e38fddd78c4a97027689ffa329e4a8e8038`.
Control Rust source: `258c685f5083c19ac238cecc0ade75dc6499f4f6`;
its crates/, programs/ and Cargo.lock bytes equal rebase candidate `3f9177b647`.
Use the unchanged `prover_rw_gate` fixture harness from each source, compiled
with `cargo build --release --locked --offline -j 4 -p aspis-r1-cost-probe
--features ct-host-prover --example prover_rw_gate`. Pin both binaries by hash
and size before entering the quiet window.

Host directory `/home/dombarker/project-offloads/codex-pv-op223-20261027/`.
Exact command after preparation:

```
ssh dombarker@100.108.41.90 'python3 /home/dombarker/project-offloads/codex-pv-op223-20261027/run_host.py quiet-timing-lead-001 '\''["python3", "/home/dombarker/project-offloads/codex-pv-op223-20261027/timing.py", "quiet-timing-lead-001-results"]'\'''
```

Pair plan: rebase timing driver, baseline first then candidate, five fresh
processes per side, identical coins 100–104; each process proves transfer and
withdrawal. Compare public.bin and proof.bin bytes for every matched fixture
and coin. Median independently per fixture must be strictly below 15 seconds
and no more than 1.10 times baseline median. Use reported prover seconds,
retain complete sample records, before/after quiet guards, host load/scope
inventories, binary pins, exact commands, and capped receipts. A populated
foreign capped scope or failed quiet guard invalidates the affected window;
do not treat its partial samples as qualified timing or rerun unchanged.

Caps: MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64, one scope.
Use the existing reservation scanner and barrier. Never remove or edit the
quiet marker; lead coordinates its lifecycle. Keep keys securely. Retain
receipts/sha256 manifests and remove only this run's raw proof corpus after
collection. No timing was run by this worker.
