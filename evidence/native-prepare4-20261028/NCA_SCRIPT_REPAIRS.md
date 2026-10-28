# Own script/harness repairs

Shared S2W backends, reservation script, launcher, shim, workspace objects and cache implementations are unchanged. Own changes only:

- mkdir(parents=True) for the lane's new scratch parent; no prover launched in the failed setup.
- Correct raw-string transport escaping in the copy setup; K001 failed its missing-source snapshot before compiler/gate. Charged conservatively.
- Cargo metadata stdout/stderr remain separated and the JSON line is parsed; frozen tuples/edges/lock validation unchanged from NBR.
- Explicit #[path] for the own private r1_wire child, then generic type parameters and Prefix impl lifetime matching. Native failed compilations receive no credit.
- Exclusive branch ownership repairs NBR_K030's E0382; mode0 was independently validated.
- Budget guards count all configured commands, including precompiler failures.
- Adaptive case batches can stop after timeout; no same-shape timeout retry is launched.
- Source-pin storage deduplicates exact repeated bytes by SHA-pinned JSON references, recording original hashes/sizes. Actual host validation is unchanged and reconstruction is checked byte-for-byte.
- Native display tail shortened only; complete raw stdout/time/metrics and errors remain in each receipt.

No timeout/cap increase, dependency drift, library-model change, or field-multiplication proof is introduced. Unwinding35 for the semantic typed-carrier harness addresses fixed array generation/copy, not a semantic buffer loop. The proposed append gate's larger unwind bound is solely harness construction of an arbitrary valid initialized live Vec prefix with uninitialized spare capacity; exactly one native push is the claimed algorithm step.

- Budget stop records are interpreted per prover, so Kani exhaustion does not block Lean.
- Default observer correction is paired with L020; arbitrary public inputs replace zeroed wrapper fixtures for the final full-route gate.

- Own SSH wrapper uses an NCA-only ControlMaster socket to reuse an authenticated connection after repeated prelaunch/recovery connection closures. Exit255 retry limits and never-resubmit semantics are unchanged; no host/lead scripts are modified.
