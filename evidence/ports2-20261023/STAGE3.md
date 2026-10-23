# Source query control for both ranges

New modules only: Port2_QuerySource and Port2_QueryAdvance isolate the inherited Stage2ContinuationQueryLoop definitions and Stage2ContinuationQueryAdvance definitions/proofs without changing their namespaces or replacing a shared olean. QuerySource retains the first definition section; QueryAdvance changes only its import and adds a provenance comment. No new extraction or source adoption is claimed.

Port2_QueryLoop.source_calls proves the complete actual emitted loop has exactly end-start ordered successful child calls. query_body_calls discharges child advancement by inversion of the inherited full opening/fold/accumulate body, for arbitrary typed QueryOps/AccumulateOps. error_stops proves an inner error executes no suffix calls. returned_next identifies the returned next field with end. The child mathematical/backend/Program interpretation remains open.

| Target | Attempt | Exit | Wall s | RSS KiB | Swap |
|---|---|---|---|---|---|
| Port2_QuerySource.lean | 007 | 0 | 1.1739013550104573 | 2634088 | 0 |
| Port2_QueryAdvance.lean | 008 | 0 | 1.7256577600055607 | 2658664 | 0 |
| Port2_QueryLoop.lean | 012 | 0 | 2.377746265992755 | 4350208 | 0 |

All accepted audits use standard axioms only. Attempts009–011 are excluded local elaboration failures (scalar comparison simplification and unfolded body equality); exact sources/errors/recovery sorryAx lines are retained. No timeout/memory kill/cap increase. Actual cumulative Lean11/100, Kani0/60; ID006 was compiler-free. Source revision, hashes, dependency object pins, toolchain/command/caps and axiom lines are in each receipt. No shipped code or ELF change.

Every lead row has its proved partial claim or exact remaining gap in design/PORTS2-20261023.md. No full row/frozen2 identity or release security claim is made.
