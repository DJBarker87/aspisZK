# Exact contract coverage

Authority: evidence/pv-runjoin6-20261026/trust-items.md, adopted by
PRIVACY-LEDGER-20261026.md, “Owner decisions 2026-10-27 (B)”, item 1.
T is exactly entropy_law, entropy_kernel, observation. No additions.

The observation field says:
`∀ c, d.nativeObservation c = d.extractedObservation c`.
Its carrier is the typed joint Observation: initial/final worlds, ordered
(pre-world, tagged call) list, filesystem State, complete D159 observer payload.
The ledger describes native getrandom/file/time/worker outcomes, filesystem
state and the complete D159 observer payload equal to extracted execution;
NOT equality with the security experiment.

This covers transferring an already-specified extracted file outcome, state
and trace to the corresponding native observation at the selected execution.
It includes failure observations and does not grant availability. It does
not define what open/write/sync/close must do. In particular, a state/world
law supplied to the extraction cannot be justified by pointing back at the
equality whose extracted side that law is supposed to define.

| Row | Covered by observation equality | Still requires a source/world P law |
|---|---|---|
| V171 op14 File.open | observed open result, state and trace, once specified | path conversion, flags, descriptor ownership, errors and state transition |
| V172 op15 sync_all | observed sync result and post-state, once specified | fsync call/error semantics; whether and what persists after crash |
| V175 op22 OpenOptions.open | observed create/open result, state and trace | option flags/mode, exclusive creation, EEXIST, shared world across calls |
| V176 op23 Error.kind | observed error kind where in execution observation | exact source representation/errno-to-kind decoding and pure frame law |
| V267 op261 write_all | observed writes, returned errors and post-state | partial progress, Interrupted retry, WriteZero, owner/cursor/contents effects |
| V268 type3 Error | observed error payload under selected interpretation | representation and payload identity, conversion and retention, no Formatter axiom |
| V271 File owner/world | observed resource and filesystem state | live descriptor ownership, aliasing, close/drop exactly once, world threading |

entropy_law and entropy_kernel grant no filesystem guarantees. In particular
neither implies exclusive creation, fsync persistence or independence of
filesystem failure from the witness.

Potential additional OS facts for owner consideration, if source/primitive
proofs cannot discharge them: open64/O_EXCL atomicity and fsync crash/recovery
persistence (including directory metadata and storage/device behavior).
They are not silently assumed here, are not new T fields and do not receive
closure credit. The finite repeated-create validation checks an ordinary
runtime behavior; it establishes no universal OS law and tests no crash.
