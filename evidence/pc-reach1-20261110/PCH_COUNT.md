Pool rows CLOSED: 39 of 278 new (A 39 / B 0 / C 0 / D 0); EXCLUDED 0 (unreachable in the deployed build; not closed); OPEN 239; target not yet established

The 39 CLOSED are inherited from PCE plus PCG; this job runs no proof gate. All 278 reachability verdicts remain UNRESOLVED. No exclusion is admitted, including live-owned and shared rows.

| Remaining OPEN class | Count | Proven REACHABLE | UNRESOLVED |
|---|---:|---:|---:|
| A | 74 | 0 | 74 |
| B | 124 | 0 | 124 |
| C | 11 | 0 | 11 |
| D | 30 | 0 | 30 |

Zero proven REACHABLE means no source instance has the required resolved MIR witness; it does not establish unreachability. LLVM diagnostic paths are retained separately.
