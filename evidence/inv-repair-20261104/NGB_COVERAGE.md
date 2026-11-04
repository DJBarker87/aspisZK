# Repaired D union Q union S coverage

599/599 rows covered by the regenerated canonical union; zero outside. Baseline: 585/587. New rows: 12, all OPEN. Historical statuses unchanged; no native closure or security premise discharge is claimed.

The NFZ_slice_build.py closure semantics are retained: per-TX shortest paths; union canonical graph; Q/S root closures; D is entry cone minus Q union S. The old exact-Q membership assertion is replaced by the complete before/after sets in NGB_LEDGER_DELTA.json. Q now includes the WideExact CodeField::from_m31 chain. Shared field embeddings formerly in D move into Q. No row is silently excluded.

NGB_COVERAGE.json records every TX occurrence, slice membership and both per-TX and canonical-union paths. 5 inherited occurrences still lack a TX-specific path; union membership is dependency coverage, not a proof of physical same-run reachability. NGB_EXCLUDED.json records the audit-only accumulation pair separately.

NFZ_C0032 remains an explicit compiler-evidence gap (statement MIR is empty); no callback edge or reachability exclusion is fabricated. Thus the 39-candidate repair is incomplete even though every current row has slice membership. Native/model callee-naming findings are in NGB_Q_CALLEE_FINDING.md; the lead owns status decisions.
