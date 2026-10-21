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
