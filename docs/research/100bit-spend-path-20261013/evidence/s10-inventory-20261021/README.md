# S10 inventory evidence

Stage 1 records the frozen source superset, the existing Stage2 LLBC call
census, and all linked function symbols/call sites in the three frozen ELFs.
This is **not complete source reachability**. The source superset includes
unreachable tests/legacy code; linked symbols omit inlined declarations;
indirect calls are not silently assumed unreachable. The direct-entrypoint
closure is a lower bound. Source hashes are read from frozen Git blobs,
not attributed to current reference additions.

`collect-host.py` reads the pinned frozen artifacts on the build host. It
checks deployed hashes and equality of linked/deployed `.text` sections,
then resolves relative SBF calls and dynamic syscall relocations. Opcode
0x8d remains an explicit indirect-call frontier. No binary or key is copied,
modified or removed. LLBC is retained on the host; only JSON census data
is committed. No proof closure or new axiom audit is claimed at this stage.

The resumed model proof is checked in `OraclePortS10ModelInventory-7/`:
`covered` covers every return continuation of the five model sites;
`interpret_eq_frozen` identifies the interpreted tree with `dV_frozen`;
`inventory_nodup` proves unique model sites; `model_S10Join` supplies the
actual `S10Join` predicate for the decision-stage tree. This excludes the
outer Rust driver, checkpoint and Pool. It is not source coverage.
Attempt 6 failed on the reserved Lean identifier `prefix`; attempt 7 renames
that binder. Attempt 5 has an interruption record and no invented timing or
exit status. All four final theorem audits use only standard axioms.

The resumed census also retains forced-Solana-cfg verifier v3, raw ELF symbol
kinds/aliases, all diagnostic source hashes, original frozen toolchain/build
metadata, and nine extraction/summary receipts. Every copied frozen input
matches the Git pin. Pool v3/v4/v5 stops record their unchanged progress or
MemoryHigh throttling; all jobs keep 6G/8G/zero-swap/64-task caps. No Pool
LLBC was emitted by these probes. No source, key or deployed artifact was
changed. Counts distinguish aliases and zero-size labels from instructions.

Reproduce the data gates without compiling or rerunning failed extractions:

```
python3 -B tools/s10-inventory-20261021/audit-extractions.py
python3 -B tools/s10-inventory-20261021/inventory.py --check
python3 -B tools/s10-inventory-20261021/audit.py
```

The final audit includes corrupt-source, linked-hash and call-target negative
tests, double-ownership detection, and the **expected exit 2** of
`inventory.py --check --require-complete`. `validation.json` records the
checks. A successful reconciliation audit does not change the incomplete
source-coverage status. The full table, residual specifications, import
collision proposal and exact open source-tree obligation are in
[S10-INVENTORY-20261021.md](../../design/S10-INVENTORY-20261021.md).
